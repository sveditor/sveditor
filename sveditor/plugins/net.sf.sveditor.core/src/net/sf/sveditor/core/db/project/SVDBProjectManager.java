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
import java.util.List;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
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
import org.eclipse.core.runtime.jobs.Job;

public class SVDBProjectManager implements 
		IResourceChangeListener, IPathVariableChangeListener {
	private LogHandle								fLog;
	private WeakHashMap<IPath, SVDBProjectData>		fProjectMap;
	private List<ISVDBProjectSettingsListener>		fListeners;
	private Job										fRefreshJob;
	private Job										fDeleteProjectJob;
	private List<IProject>							fChangedProjects;
	private List<IProject>							fDeletedProjects;
	
	public SVDBProjectManager() {
		fLog = LogFactory.getLogHandle("SVDBProjectManager");
		fProjectMap = new WeakHashMap<IPath, SVDBProjectData>();
		fListeners = new ArrayList<ISVDBProjectSettingsListener>();
//		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		fChangedProjects = new ArrayList<IProject>();
		fDeletedProjects = new ArrayList<IProject>();
		
		IPathVariableManager pvm = ResourcesPlugin.getWorkspace().getPathVariableManager();
		pvm.addChangeListener(this);
	}

	/**
	 * Initialize SV projects in the workspace
	 */
	public void init() {
		fProjectMap.clear();
		
		SVDBInitProjectsJob job = new SVDBInitProjectsJob();
		// Ensure this job is sensitive to the workspace
		job.setRule(ResourcesPlugin.getWorkspace().getRoot());
		
		job.schedule();
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
		SVDBOpenProjectJob job = new SVDBOpenProjectJob(p);
		job.setRule(ResourcesPlugin.getWorkspace().getRoot());
		job.schedule();
	}
	
	public void projectClosed(IProject p) {
		if (fProjectMap.containsKey(p)) {
			// Start a job to clean up after the specified project
		}
	}
	
	public void projectRemoved(IProject p) {
		if (fProjectMap.containsKey(p)) {
			SVDBRemoveProjectJob job = new SVDBRemoveProjectJob(fProjectMap.get(p));
			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.schedule();
		}
	}
	
	void projectSettingsChanged(SVDBProjectData data) {
		synchronized (fListeners) {
			for (int i=0; i<fListeners.size(); i++) {
				fListeners.get(i).projectSettingsChanged(data);
			}
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
	public synchronized SVDBProjectData getProjectData(IProject proj) {
		SVDBProjectData ret = null;
		
		if (fProjectMap.containsKey(proj.getFullPath())) {
			ret = fProjectMap.get(proj.getFullPath());
		} else if (proj.exists()) {
			/*
			IFile svproject;
			SVProjectFileWrapper f_wrapper = null;
			if ((svproject = proj.getFile(".svproject")).exists()) {
				InputStream in = null;
				try {
					svproject.refreshLocal(IResource.DEPTH_ZERO, null);
					in = svproject.getContents();
				} catch (CoreException e) {
					e.printStackTrace();
				}

				try {
					f_wrapper = new SVProjectFileWrapper(in);
				} catch (Exception e) {
					// File format is bad
					f_wrapper = null;
				}
			}
			
			if (f_wrapper == null) {
				f_wrapper = new SVProjectFileWrapper();
				
				setupDefaultProjectFile(f_wrapper);
				
				// Write the file
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				f_wrapper.toStream(bos);
				ByteArrayInputStream bis = new ByteArrayInputStream(bos.toByteArray());
				
				try {
					if (svproject.exists()) {
						svproject.setContents(bis, true, true, null);
					} else {
						svproject.create(bis, true, null);
					}
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
			 */
			
			ret = new SVDBProjectData(proj);
			
			fProjectMap.put(proj.getFullPath(), ret);
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
				fRefreshJob.setRule(ResourcesPlugin.getWorkspace().getRoot());
				fRefreshJob.schedule(100);
			}
		}
		
		synchronized (fDeletedProjects) {
			if (fDeletedProjects.size() > 0 && fDeleteProjectJob == null) {
				fDeleteProjectJob = new DeleteProjectJob();
				fDeleteProjectJob.setRule(ResourcesPlugin.getWorkspace().getRoot());
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
//		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}
}
