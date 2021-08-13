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


package org.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.sveditor.core.db.index.SVDBIndexChangeEvent;
import org.sveditor.core.db.project.ISVDBProjectSettingsListener;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.project.SVDBProjectManager;
import org.sveditor.core.dirtree.SVDBDirTreeNode;
import org.sveditor.core.job_mgr.IJob;
import org.sveditor.core.job_mgr.IJobMgr;
import org.eclipse.jface.viewers.IElementComparer;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

public class ProjectPathsContentProvider implements 
		ISVDBProjectSettingsListener, ISVDBIndexChangeListener, 
		ITreeContentProvider, IProjectPathsData {
	private List<ProjectPathsData>				fProjectDataMap;
	public static final Object 					NO_ELEMENTS[] = new Object[0];
	private TreeViewer							fViewer;
	private boolean								fRefreshQueued;
	private IElementComparer					fDefaultComparer;
	
	public ProjectPathsContentProvider() {
		fProjectDataMap = new ArrayList<ProjectPathsData>();
	}
	
	@Override
	public String getName() {
		return "Root";
	}

	public void reset() { }

	@Override
	public boolean hasChildren() {
		return true;
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IProject &&
				((IProject)parentElement).getFile(".svproject").exists()) {
			SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(
					(IProject)parentElement);
			ProjectPathsData paths_d = getProjectPathsData(pd);
			
			if (paths_d == null) {
				// Not available, or not available yet
				return new Object[0];
			} else {
				return new Object[] {paths_d};
			}
		} else if (parentElement instanceof IProjectPathsData) {
			return ((IProjectPathsData)parentElement).getChildren(parentElement);
		} else if (parentElement instanceof SVDBDirTreeNode) {
			return ((SVDBDirTreeNode)parentElement).getChildren().toArray();
		}
		return NO_ELEMENTS;
	}
	
	private ProjectPathsData getProjectPathsData(final SVDBProjectData pd) {
		int idx;
		
		synchronized (fProjectDataMap) {
			ProjectPathsData tmp = new ProjectPathsData(fViewer, pd, false);
			idx = fProjectDataMap.indexOf(tmp);
		}
		
		if (idx == 0) {
			return fProjectDataMap.get(idx);
		} else if (idx == -1) {
			synchronized (fProjectDataMap) {
				while (fProjectDataMap.size() >= 15) {
					// Remove
					ProjectPathsData paths_d = fProjectDataMap.remove(0);
					removeListeners(paths_d.getProjectData());
				}
			}
			
			// We don't currently have the project data. Create a new
			// instance in a thread
			IJobMgr job_mgr = SVCorePlugin.getJobMgr();
			IJob job = job_mgr.createJob();
			
			job.init("get project data", new Runnable() {
				
				public void run() {
					// Time-consuming operation
					ProjectPathsData paths_d = new ProjectPathsData(fViewer, pd);
					addListeners(pd);
					synchronized (fProjectDataMap) {
						fProjectDataMap.add(paths_d);
					}
			
					Display d = fViewer.getControl().getDisplay();
					if (d != null && !d.isDisposed() && !fViewer.getControl().isDisposed()) {
						// Notify the viewer that it must update
						fViewer.getControl().getDisplay().asyncExec(new Runnable() {
							public void run() {
								fViewer.refresh();
							}
						});
					}
				}
			});
			job_mgr.queueJob(job);
			
			return null;
		} else {
			ProjectPathsData paths_d = fProjectDataMap.remove(idx);
			fProjectDataMap.add(paths_d);
			return paths_d;
		}
	}
	
	private void addListeners(SVDBProjectData pd) {
		pd.addProjectSettingsListener(this);
		pd.getProjectIndexMgr().addIndexChangeListener(this);
	}
	
	private void removeListeners(SVDBProjectData pd) {
		pd.removeProjectSettingsListener(this);
		pd.getProjectIndexMgr().removeIndexChangeListener(this);
	}

	public Object getParent(Object element) {
		if (element instanceof IProjectPathsData) {
			return ((IProjectPathsData)element).getParent(element);
		} else if (element instanceof LibIndexPath) {
			LibIndexPath lip = (LibIndexPath)element;
			return lip.getParent(element);
		} else if (element instanceof SVDBDirTreeNode) {
			return ((SVDBDirTreeNode)element).getParent();
		} else {
			return null;
		}
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

	public Object[] getElements(Object inputElement) {
		return NO_ELEMENTS;
	}

	public void dispose() {
		if (fViewer != null && !fViewer.getControl().isDisposed()) {
			((TreeViewer)fViewer).setComparer(fDefaultComparer);
		}
	}
	
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fViewer = (TreeViewer)viewer;
	}

	
	@Override
	public void index_event(SVDBIndexChangeEvent e) {
		doRefresh();
	}

	public void projectSettingsChanged(SVDBProjectData data) {
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		if (!pmgr.isManagedProject(data.getProject())) {
			// Project was deleted
		}
		doRefresh();
	}
	
	private void doRefresh() {
		if (!fRefreshQueued && fViewer != null && !fViewer.getControl().isDisposed()) {
			fRefreshQueued = true;
			fViewer.getControl().getDisplay().asyncExec(new Runnable() {
				public void run() {
					fViewer.refresh();
					fRefreshQueued = false;
				}
			});
		}
	}
}
