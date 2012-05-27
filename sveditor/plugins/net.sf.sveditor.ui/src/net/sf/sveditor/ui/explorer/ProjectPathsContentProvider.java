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


package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.project.ISVDBProjectSettingsListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IElementComparer;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

public class ProjectPathsContentProvider implements 
		ITreeContentProvider, ISVDBProjectSettingsListener, ISVDBIndexChangeListener {
	private List<ProjectPathsData>				fProjectDataMap;
	private static Object 						NO_ELEMENTS[] = new Object[0];
	private Viewer								fViewer;
	private boolean							fRefreshQueued;
	private IElementComparer					fDefaultComparer;
	
	public ProjectPathsContentProvider() {
		fProjectDataMap = new ArrayList<ProjectPathsData>();
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IProject &&
				((IProject)parentElement).getFile(".svproject").exists()) {
			SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(
					(IProject)parentElement);
			ProjectPathsData paths_d = getProjectPathsData(pd);
			return new Object[] {paths_d};
		} else if (parentElement instanceof IProjectPathsData) {
			return ((IProjectPathsData)parentElement).getChildren(parentElement);
		}
		return NO_ELEMENTS;
	}
	
	private ProjectPathsData getProjectPathsData(SVDBProjectData pd) {
		int idx = fProjectDataMap.indexOf(pd);
		
		if (idx == 0) {
			return fProjectDataMap.get(idx);
		} else if (idx == -1) {
			while (fProjectDataMap.size() >= 15) {
				// Remove
				ProjectPathsData paths_d = fProjectDataMap.remove(0);
				removeListeners(paths_d.getProjectData());
			}
			ProjectPathsData paths_d = new ProjectPathsData(pd);
			addListeners(pd);
			return paths_d;
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
		if (element instanceof LibIndexPath) {
			LibIndexPath lip = (LibIndexPath)element;
			return lip.getParent(element);
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
		fViewer = viewer;
	}

	public void index_changed(int reason, SVDBFile file) {
		doRefresh();
	}

	public void index_rebuilt() {
		doRefresh();
	}

	public void projectSettingsChanged(SVDBProjectData data) {
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
