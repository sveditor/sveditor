/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IPathVariableChangeEvent;
import org.eclipse.core.resources.IPathVariableChangeListener;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVMarkers;
import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.builder.SafeSVBuilderOutput;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexStatsProvider;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.ops.SVDBClearMarkersOp;
import net.sf.sveditor.core.db.index.ops.SVDBPropagateMarkersOp;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBProjectManager implements 
		IResourceChangeListener, IPathVariableChangeListener,
		ILogLevel {
	private static final int						BUILD_DELAY = 5000;
	private static final int						INIT_DELAY = 1000;
	private LogHandle								fLog;
	private WeakHashMap<IPath, SVDBProjectData>		fProjectMap;
	private List<ISVDBProjectSettingsListener>		fListeners;
	private Job										fRefreshJob;
	private Job										fDeleteProjectJob;
	private List<IProject>							fChangedProjects;
	private List<IProject>							fDeletedProjects;
	private Set<IProject>							fBuildActiveProjects;
	private Set<ISVProjectDelayedOp>				fDelayedOpList;
	
	public SVDBProjectManager() {
		fLog = LogFactory.getLogHandle("SVDBProjectManager");
		fProjectMap = new WeakHashMap<IPath, SVDBProjectData>();
		fListeners = new ArrayList<ISVDBProjectSettingsListener>();
		fChangedProjects = new ArrayList<IProject>();
		fDeletedProjects = new ArrayList<IProject>();
		
		fBuildActiveProjects = new HashSet<IProject>();
		fDelayedOpList = new HashSet<ISVProjectDelayedOp>();
		
		IPathVariableManager pvm = ResourcesPlugin.getWorkspace().getPathVariableManager();
		pvm.addChangeListener(this);
	}
	
	/**
	 * Initialize SV projects in the workspace
	 */
	public void init() {
		fProjectMap.clear();

		SVDBInitProjectsJob job = new SVDBInitProjectsJob(this);
		// Ensure this job is sensitive to the workspace
//		job.setRule(ResourcesPlugin.getWorkspace().getRoot());
		
		launchDelayedBuild(job);

		job.schedule(INIT_DELAY);
	}

	public static boolean isSveProject(IProject p) {
		return p.getFile(new Path(".svproject")).exists();
	}
	
	public void addProjectSettingsListener(ISVDBProjectSettingsListener l) {
		synchronized (fListeners) {
			fListeners.add(l);
		}
	}
	
	public void removeProjectSettingsListener(ISVDBProjectSettingsListener l) {
		synchronized (fListeners) {
			fListeners.remove(l);
		}
	}
	
	public void startBuild(
			Process					process,
			IProject 				project,
			int						kind,
			Map<String, String>		args) {
		SVCorePlugin.getDefault().getBuildProcessListener().buildProcess(process);
		buildEvent(project, true, kind, args);
	}
	
	public void endBuild(
			IProject 				project,
			int						kind,
			Map<String, String>		args) {
		buildEvent(project, false, kind, args);
	}
	
	public void buildEvent(
			IProject			project,
			boolean				started,
			int					kind,
			Map<String, String>	args) {
		SVDBProjectData pd = fProjectMap.get(project.getFullPath());
		if (pd != null) {
			pd.buildEvent(started, kind, args);
		}
	}
	
	public void projectOpened(IProject p) {
		// Start a job to handle the fact that a project is opening
		boolean is_sve_project = SVDBProjectManager.isSveProject(p);
		
		fLog.debug(LEVEL_MIN, "projectOpened: " + p.getName() + " is_sve_project=" + is_sve_project);
		

		if (is_sve_project) {
			// Ensure the project nature is associated
//			SVProjectNature.ensureHasSvProjectNature(p);
			fLog.debug(LEVEL_MIN, "  -- is SVE project");
			
		
			SVDBOpenProjectJob job = new SVDBOpenProjectJob(this, p);
//			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
//			job.schedule(BUILD_DELAY);
//			job.schedule();
			
			SVDBRefreshDoneJobWrapper jw = new SVDBRefreshDoneJobWrapper(
					job, BUILD_DELAY);
			jw.schedule();
			
			synchronized (fDelayedOpList) {
				fDelayedOpList.add(job);
			}
		} else {
			fLog.debug(LEVEL_MIN, "  -- not SVE project");
		}
	}
	
	public void projectClosed(IProject p) {
		if (fProjectMap.containsKey(p.getFullPath())) {
			// Start a job to clean up after the specified project
			SVDBRemoveProjectJob job = new SVDBRemoveProjectJob(
					fProjectMap.get(p.getFullPath()));
//			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.schedule();
			
			fProjectMap.remove(p.getFullPath());
		}
	}
	
	public void projectRemoved(IProject p) {
		if (fProjectMap.containsKey(p.getFullPath())) {
			SVDBRemoveProjectJob job = new SVDBRemoveProjectJob(
					fProjectMap.get(p.getFullPath()));
//			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.schedule();
			fProjectMap.remove(p.getFullPath());
		}
	}
	
	void startDelayedBuild(ISVProjectDelayedOp op) {
		synchronized (fDelayedOpList) {
			fDelayedOpList.remove(op);
		}
	}
	
	void launchDelayedBuild(ISVProjectDelayedOp op) {
		synchronized (fDelayedOpList) {
			fDelayedOpList.add(op);
		}
	}
	
	void projectSettingsChanged(SVDBProjectData data) {
		synchronized (fListeners) {
			for (int i=0; i<fListeners.size(); i++) {
				fListeners.get(i).projectSettingsChanged(data);
			}
		}
	}
	
	public boolean rebuildProject(
			IProgressMonitor 		monitor, 
			IProject 				p) {
		return rebuildProject(monitor, p, 
				new SafeSVBuilderOutput(null));
	}
	
	public boolean rebuildProject(
			IProgressMonitor 		monitor, 
			IProject 				p,
			ISVBuilderOutput		out) {
		return rebuildProject(monitor, p, false, out);
	}
	
	public boolean rebuildProject(
			IProgressMonitor 		monitor, 
			IProject 				p, 
			boolean 				wait_for_refresh) {
		return rebuildProject(monitor, p, wait_for_refresh, 
				new SafeSVBuilderOutput(null));
	}

	/**
	 * Note: 
	 * @param monitor
	 * @param p
	 * @param wait_for_refresh
	 * @return
	 */
	public boolean rebuildProject(
			IProgressMonitor 		monitor, 
			IProject 				p, 
			boolean 				wait_for_refresh,
			ISVBuilderOutput		out) {
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		if (!isSveProject(p)) {
			// This is likely an auto-build occurring in the middle of import
			out.note("rebuildProject: cancel due to !isSveProject");
			return false;
		}
	
		if (SVDBRefreshDoneJobWrapper.isRefreshRunning()) {
			if (wait_for_refresh) {
				do {
					try {
						Thread.sleep(1000);
					} catch (InterruptedException e) {}
				} while (SVDBRefreshDoneJobWrapper.isRefreshRunning() &&
						!subMonitor.isCanceled());
				
				if (SVDBRefreshDoneJobWrapper.isRefreshRunning()) {
					// 
					return false;
				}
			} else {
			/*
			 */
				out.note("rebuildProject: cancel due to RefreshJob running");
				return false;
			}
		}
		
		synchronized (fDelayedOpList) {
			for (ISVProjectDelayedOp op : fDelayedOpList) {
				op.projectBuildStarted(p);
			}
		}
		
		synchronized (fBuildActiveProjects) {
			fBuildActiveProjects.add(p);
		}
		
		SVDBProjectData pd = getProjectData(p);
		if (pd != null) {
			// Ensure we're up-to-date
			pd.refresh();
			
			boolean have_stats = false;
			SVDBIndexStats stats = new SVDBIndexStats();
			SVDBIndexCollection index = pd.getProjectIndexMgr();
			List<ISVDBIndex> index_l = index.getIndexList();
			subMonitor.beginTask("Build " + p.getName(), 12000*(index_l.size()+1));
			
			for (ISVDBIndex i : index_l) {
				subMonitor.subTask("Build " + i.getBaseLocation());
				SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(i);
				
				out.note("Rebuild index " + i.getBaseLocation());
				
				i.execOp(subMonitor.newChild(1000), 
						new SVDBClearMarkersOp(), false);
				if (subMonitor.isCanceled()) {
					break;
				}

				i.setBuilderOutput(out);
				i.execIndexChangePlan(subMonitor.newChild(10000), plan);
				i.setBuilderOutput(null);
				if (subMonitor.isCanceled()) {
					break;
				}

				i.execOp(subMonitor.newChild(1000),
						new SVDBPropagateMarkersOp(), false);
				if (subMonitor.isCanceled()) {
					break;
				}
				
				if (i instanceof ISVDBIndexStatsProvider) {
					SVDBIndexStats i_stats = ((ISVDBIndexStatsProvider)i).getIndexStats();
					stats.add(i_stats);
					have_stats = true;
				}
			}
			
			if (have_stats) {
				out.note("Index Statistics: " +
						SVDBIndexStats.calcNPerS(stats.getNumLines(),  stats.getLastIndexTotalTime()) +
						" Lines per second");
				out.note("  Root Files: " + stats.getNumRootFiles());
				out.note("  Total Files: " + stats.getNumProcessedFiles());
				out.note("  Total Lines: " + stats.getNumLines());
				out.note("  File Read Time: " + stats.getLastIndexFileReadTime() + "ms");
				out.note("  Pre-Process Time: " + stats.getLastIndexPreProcessTime() + "ms");
				out.note("  Parse Time: " + stats.getLastIndexParseTime() + "ms");
				out.note("  Ref-Cache Time: " + stats.getLastIndexRefCacheTime() + "ms");
				out.note("  Decl-Cache Time: " + stats.getLastIndexDeclCacheTime() + "ms");
				out.note("  Total Index Time: " + stats.getLastIndexTotalTime() + "ms");
			}
			
			// Finally, update the markers

		} else {
			fLog.debug("ProjectData null");
			subMonitor.done();
			return false;
		}
		
		// Fire one more time to catch requests that 
		// might have accumulated
		synchronized (fDelayedOpList) {
			for (ISVProjectDelayedOp op : fDelayedOpList) {
				op.projectBuildStarted(p);
			}
		}
		
		subMonitor.done();
		
		synchronized (fBuildActiveProjects) {
			fBuildActiveProjects.remove(p);
		}
		
		return true;
	}

	public void rebuildProject(
			IProgressMonitor 					monitor,
			IProject 							p,
			List<SVDBIndexResourceChangeEvent> 	changes,
			ISVBuilderOutput					out) {
		boolean full_build = false;
		boolean rebuild_workspace = false;
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		if (!isSveProject(p)) {
			// Likely an auto-build mid-import
			return;
		}
		
		for (Job j : Job.getJobManager().find(null)) {
			fLog.debug(LEVEL_MIN, "Job: " + j.getName());
			if (j.getName().startsWith("Building work")) {
				if (j.getThread() != Thread.currentThread()) {
					rebuild_workspace = true;
				}
				break;
			}
		}

		if (rebuild_workspace) {
			out.note("Skip due to rebuild workspace");
			return;
		}
		
		synchronized (fDelayedOpList) {
			// A delayed op supercedes an incremental build
			for (ISVProjectDelayedOp op : fDelayedOpList) {
				if (op.containsProject(p)) {
					return;
				}
			}
		}
		
		SVDBProjectData pd = getProjectData(p);
		if (pd != null) {
			SVDBIndexCollection index = pd.getProjectIndexMgr();
			List<ISVDBIndex> index_l = index.getIndexList();
			subMonitor.beginTask("Build " + p.getName(), 12000*index_l.size());
			
			for (ISVDBIndex i : index_l) {
				i.setBuilderOutput(out);
			}
			
			for (ISVDBIndex i : index_l) {
				SubMonitor loopMonitor = subMonitor.newChild(12000);
				loopMonitor.setTaskName("Build " + i.getBaseLocation());
				loopMonitor.setWorkRemaining(12000);
				ISVDBIndexChangePlan plan = i.createIndexChangePlan(changes);
			
				try {
					p.deleteMarkers(SVMarkers.TYPE_PROBLEM, true, IResource.DEPTH_ZERO);
				} catch (CoreException e) {}
				
				if (plan != null && plan.getType() != SVDBIndexChangePlanType.Empty) {
					full_build = (plan.getType() == SVDBIndexChangePlanType.RebuildIndex);
					i.execOp(loopMonitor.newChild(1000), 
							new SVDBClearMarkersOp(), true);
					if (loopMonitor.isCanceled()) {
						break;
					}
					i.execIndexChangePlan(loopMonitor.newChild(10000), plan);
					if (loopMonitor.isCanceled()) {
						break;
					}
					i.execOp(loopMonitor.newChild(1000),
							new SVDBPropagateMarkersOp(), false);
					if (loopMonitor.isCanceled()) {
						break;
					}
				} else {
					loopMonitor.worked(12000); // Nothing to do for this index
				}
				
			}
			
			for (ISVDBIndex i : index_l) {
				i.setBuilderOutput(null);
			}
			
			if (full_build) {
				// Fire one more time to catch requests that 
				// might have accumulated
				synchronized (fDelayedOpList) {
					for (ISVProjectDelayedOp op : fDelayedOpList) {
						op.projectBuildStarted(p);
					}
				}
			}
			
			subMonitor.done();
		}
	}
	
	public List<SVDBProjectData> getProjectList() {
		List<SVDBProjectData> ret = new ArrayList<SVDBProjectData>();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		for (IProject p : root.getProjects()) {
			if (p.isOpen() && p.getFile(".svproject").exists()) {
				SVDBProjectData pd = getProjectData(p);
				if (pd != null) {
					ret.add(pd);
				}
			}
		}
		
		return ret;
	}
	
	public static boolean isSVProject(IProject p) {
		if (p.isAccessible() && p.isOpen()) {
			IFile svproject = p.getFile(".svproject");
			if (svproject.exists() && svproject.isAccessible()) {
				return true;
			}
		} 
		return false;
	}
	
	public boolean isManagedProject(IProject proj) {
		return (fProjectMap.containsKey(proj.getFullPath()));
	}

	/**
	 * 
	 * @param proj
	 * @return
	 */
	public SVDBProjectData getProjectData(IProject proj) {
		SVDBProjectData ret = null;
		
		synchronized (fProjectMap) {
			if (fProjectMap.containsKey(proj.getFullPath())) {
				ret = fProjectMap.get(proj.getFullPath());
			}
		}
		
		if (ret == null && proj.exists()) {
			
			ret = new SVDBProjectData(proj);

			synchronized (fProjectMap) {
				fProjectMap.put(proj.getFullPath(), ret);
			}
		}
		
		return ret;
	}

	/**
	 * Setup the default project data.
	 * - Includes default plugin libraries
	 * 
	 * @param file_wrapper
	 */
	public static void setupDefaultProjectFile(SVProjectFileWrapper file_wrapper) {
		List<SVDBPluginLibDescriptor> lib_d = SVCorePlugin.getDefault().getPluginLibList();
		
		for (SVDBPluginLibDescriptor d : lib_d) {
			if (d.isDefault()) {
				file_wrapper.getPluginPaths().add(new SVDBPath(d.getId()));
			}
		}
	}
	
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getDelta() != null) {
			try {
				event.getDelta().accept(new IResourceDeltaVisitor() {
					public boolean visit(IResourceDelta delta)
							throws CoreException {
						IProject p = null;
						if (delta.getResource().getType() == IResource.PROJECT) {
							// Project is changing
							if (delta.getKind() == IResourceDelta.REMOVED) {
								synchronized (fDeletedProjects) {
									p = (IProject)delta.getResource();
									if (!SVCorePlugin.getTestMode()) {
									if (!fDeletedProjects.contains(p)) {
										fDeletedProjects.add(p);
									}
									}
								}
							} else if (delta.getKind() == IResourceDelta.ADDED) {
								
							}
						} else {
							p = delta.getResource().getProject();
							if (p != null && fProjectMap.containsKey(p.getFullPath())) {
								if (delta.getKind() != IResourceDelta.REMOVED) {
									String name = delta.getResource().getName();

									if (name.equals(".project") || name.equals(".svproject")) {
										synchronized (fChangedProjects) {
											if (!SVCorePlugin.getTestMode()) {
											if (!fChangedProjects.contains(p)) {
												fChangedProjects.add(p);
											}
											}
										}
									}
								}
							}
						}
						return true;
					}
				});
			} catch (CoreException e) {
			}
		}
		
		
		
		synchronized (fChangedProjects) {
			if (fChangedProjects.size() > 0 && fRefreshJob == null) {
				// Launch a new job
				fRefreshJob = new RefreshJob();
				// Cannot run this job until the workspace is free
//				fRefreshJob.setRule(ResourcesPlugin.getWorkspace().getRoot());
				fRefreshJob.schedule(100);
			}
		}
		
		synchronized (fDeletedProjects) {
			if (fDeletedProjects.size() > 0 && fDeleteProjectJob == null) {
				fDeleteProjectJob = new DeleteProjectJob();
//				fDeleteProjectJob.setRule(ResourcesPlugin.getWorkspace().getRoot());
				fDeleteProjectJob.schedule(100);
			}
		}
	}
	
	public void pathVariableChanged(IPathVariableChangeEvent event) {
//		System.out.println("pathVariableChanged");
	}

	private class RefreshJob extends Job {
		
		public RefreshJob() {
			super("SVDBProjectManager.RefreshJob");
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			while (true) {
				IProject project = null;
				if (monitor.isCanceled()) {
					break;
				}
				
				synchronized (fChangedProjects) {
					if (fChangedProjects.size() == 0) {
						fRefreshJob = null;
					} else {
						project = fChangedProjects.remove(0);
					}
				}
				
				if (project != null) {
					SVDBProjectData pd = fProjectMap.get(project.getFullPath());
					
					// Only refresh if the project-file wrapper detects
					// that something has changed
					pd.setProjectFileWrapper(pd.getProjectFileWrapper(), false);
				
					// Notify listeners that something has changed
					projectSettingsChanged(pd);
				} else {
					break;
				}
			}
			
			return Status.OK_STATUS;
		}
	}
	
	private class DeleteProjectJob extends Job {
		
		public DeleteProjectJob() {
			super("SVDBProjectManager.DeleteProjectJob");
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			
			while (true) {
				IProject p = null;

				if (monitor.isCanceled()) {
					break;
				}
			
				synchronized (fDeletedProjects) {
					if (fDeletedProjects.size() > 0) {
						p = fDeletedProjects.remove(0);
					} else {
						fDeleteProjectJob = null;
					}
				}

				if (p != null) {
					SVDBProjectData pd = getProjectData(p);
					fLog.debug("Deleting project data for \"" + p.getName() + "\"");
					
					if (pd != null) {
						SVDBIndexCollection index_collection = pd.getProjectIndexMgr();
						SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
						List<ISVDBIndex> index_list = index_collection.getIndexList();
						
						for (ISVDBIndex index : index_list) {
							rgy.disposeIndex(index, "Removing deleted-project indexes");
						}
					} else {
						fLog.debug("Project data already null");
					}
				} else {
					break;
				}
			}

			return Status.OK_STATUS;
		}
		
	}
	
	public void dispose() {
		fProjectMap.clear();
	}
}
