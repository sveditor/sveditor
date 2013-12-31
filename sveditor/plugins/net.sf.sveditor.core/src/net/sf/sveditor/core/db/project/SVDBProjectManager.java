/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.WeakHashMap;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVMarkers;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.ops.SVDBClearMarkersOp;
import net.sf.sveditor.core.db.index.ops.SVDBPropagateMarkersOp;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

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
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

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
		if (fProjectMap.containsKey(p)) {
			// Start a job to clean up after the specified project
			SVDBRemoveProjectJob job = new SVDBRemoveProjectJob(fProjectMap.get(p));
//			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.schedule();
			
			fProjectMap.remove(p);
		}
	}
	
	public void projectRemoved(IProject p) {
		if (fProjectMap.containsKey(p)) {
			SVDBRemoveProjectJob job = new SVDBRemoveProjectJob(fProjectMap.get(p));
//			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.schedule();
			fProjectMap.remove(p);
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
	
	public void rebuildProject(IProgressMonitor monitor, IProject p) {
		
		if (!isSveProject(p)) {
			// This is likely an auto-build occurring in the middle of import
			fLog.debug("rebuildProject: cancel due to !isSveProject");
			return;
		}
		
		if (SVDBRefreshDoneJobWrapper.isRefreshRunning()) {
			fLog.debug("rebuildProject: cancel due to RefreshJob running");
			return;
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
			
			SVDBIndexCollection index = pd.getProjectIndexMgr();
			List<ISVDBIndex> index_l = index.getIndexList();
			monitor.beginTask("Build " + p.getName(), 12000*(index_l.size()+1));
			
			for (ISVDBIndex i : index_l) {
				monitor.subTask("Build " + i.getBaseLocation());
				SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(i);
				
				fLog.debug(LEVEL_MID, "Rebuild index " + i.getBaseLocation());
				
				i.execOp(new SubProgressMonitor(monitor, 1000), 
						new SVDBClearMarkersOp(), false);
				if (monitor.isCanceled()) {
					break;
				}
				
				i.execIndexChangePlan(new SubProgressMonitor(monitor, 10000), plan);
				if (monitor.isCanceled()) {
					break;
				}

				i.execOp(new SubProgressMonitor(monitor, 1000),
						new SVDBPropagateMarkersOp(), false);
				if (monitor.isCanceled()) {
					break;
				}
			}
			
			// Finally, update the markers

		} else {
			System.out.println("ProjectData null");
		}

		// Fire one more time to catch requests that 
		// might have accumulated
		synchronized (fDelayedOpList) {
			for (ISVProjectDelayedOp op : fDelayedOpList) {
				op.projectBuildStarted(p);
			}
		}
		
		monitor.done();
		
		synchronized (fBuildActiveProjects) {
			fBuildActiveProjects.remove(p);
		}
	}

	public void rebuildProject(
			IProgressMonitor 					monitor, 
			IProject 							p,
			List<SVDBIndexResourceChangeEvent> 	changes) {
		boolean full_build = false;
		boolean rebuild_workspace = false;
		
		for (Job j : Job.getJobManager().find(null)) {
			System.out.println("Job: " + j.getName());
			if (j.getName().startsWith("Building work")) {
				rebuild_workspace = true;
				break;
			}
		}

		if (rebuild_workspace) {
			fLog.debug(LEVEL_MIN, "Skip due to rebuild workspace");
			return;
		}
		
		if (!isSveProject(p)) {
			// Likely an auto-build mid-import
			return;
		}

		
		synchronized (fDelayedOpList) {
			// A delayed op supercedes an incremental build
			if (fDelayedOpList.contains(p)) {
				return;
			}
		}
		
		SVDBProjectData pd = getProjectData(p);
		if (pd != null) {
			SVDBIndexCollection index = pd.getProjectIndexMgr();
			List<ISVDBIndex> index_l = index.getIndexList();
			monitor.beginTask("Build " + p.getName(), 12000*index_l.size());
			
			for (ISVDBIndex i : index_l) {
				monitor.subTask("Build " + i.getBaseLocation());
				ISVDBIndexChangePlan plan = i.createIndexChangePlan(changes);
			
				try {
					p.deleteMarkers(SVMarkers.TYPE_PROBLEM, true, IResource.DEPTH_ZERO);
				} catch (CoreException e) {}
				
				if (plan != null && plan.getType() != SVDBIndexChangePlanType.Empty) {
					full_build = (plan.getType() == SVDBIndexChangePlanType.RebuildIndex);
					i.execOp(new SubProgressMonitor(monitor, 1000), 
							new SVDBClearMarkersOp(), true);
					if (monitor.isCanceled()) {
						break;
					}
					i.execIndexChangePlan(new SubProgressMonitor(monitor, 10000), plan);
					if (monitor.isCanceled()) {
						break;
					}
					i.execOp(new SubProgressMonitor(monitor, 1000),
							new SVDBPropagateMarkersOp(), false);
					if (monitor.isCanceled()) {
						break;
					}
				} else {
					monitor.worked(20000); // Nothing to do for this index
				}
				
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
			
			monitor.done();
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
