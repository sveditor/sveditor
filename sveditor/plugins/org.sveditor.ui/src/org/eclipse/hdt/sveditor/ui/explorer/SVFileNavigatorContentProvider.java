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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.ISVDBScopeItem;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBTask;
import org.sveditor.core.db.index.ISVDBChangeListener;
import org.sveditor.core.db.project.ISVDBProjectSettingsListener;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.search.SVDBSearchResult;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

public class SVFileNavigatorContentProvider 
	implements ITreeContentProvider, Runnable, ISVDBChangeListener,
		ISVDBProjectSettingsListener {
	
	private Viewer									fViewer;
	private LogHandle								fLog;
	
	public SVFileNavigatorContentProvider() {
		SVCorePlugin.getDefault().getProjMgr().addProjectSettingsListener(this);
		fLog = LogFactory.getLogHandle("SVFileNavigatorContentProvider");
	}
	
	public void SVDBFileChanged(
			SVDBFile 			file, 
			List<SVDBItem> 		adds,
			List<SVDBItem> 		removes, 
			List<SVDBItem> 		changes) {
		Display.getDefault().asyncExec(this);
	}
	
	public void projectSettingsChanged(SVDBProjectData data) {
		// refresh, just in case the new index allows us
		// to display structure information where we couldn't 
		// previously
		fLog.debug("Project settings changed -- refreshing");
		Display.getDefault().asyncExec(this);
	}


	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFile) {
//			IFile file = (IFile)parentElement;
//			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
//			SVDBProjectData pdata = pmgr.getProjectData(file.getProject());
//			SVDBIndexCollectionMgr index_mgr = pdata.getProjectIndexMgr();
			
			List<SVDBSearchResult<SVDBFile>> res = new ArrayList<SVDBSearchResult<SVDBFile>>();
// TODO: File-structure display disabled for now
//				index_mgr.findFile("${workspace_loc}" + file.getFullPath());
			
			SVDBFile svdb_file = null;
			if (res.size() == 0) {
				// If the file is not currently included in an index, then don't
				// try to fix things up. We don't want to accidentally start parsing
				// large numbers of files
				/*
				SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
				ISVDBIndex index = rgy.findCreateIndex(
						file.getProject().getName(),
						"${workspace_loc}" + file.getParent().getFullPath().toOSString(),
						SVDBSourceCollectionIndexFactory.TYPE, null);
				index_mgr.addShadowIndex(index.getBaseLocation(), index);
				
				res = index_mgr.findFile("${workspace_loc}" + file.getFullPath());
				if (res.size() > 0) {
					svdb_file = res.get(0).getItem();
				} else {
					fLog.error("Failed to find \"" + file.getFullPath() + "\" even after " +
							"adding a shadow index");
				}
				 */
			} else {
				svdb_file = res.get(0).getItem();
			}
			
			
			if (svdb_file != null) {
				List<SVDBItem> ret = new ArrayList<SVDBItem>();
				
				for (ISVDBItemBase it : svdb_file.getChildren()) {
					if (it.getType() != SVDBItemType.Marker) {
						ret.add((SVDBItem)it);
					}
				}
				
				return ret.toArray();
			} else {
				return new Object[0];
			}
		} else if (parentElement instanceof ISVDBScopeItem &&
				!(parentElement instanceof SVDBTask)) {
			return ((ISVDBScopeItem)parentElement).getItems().toArray();
		}
		
		return new Object[0];
	}

	
	public Object getParent(Object element) {
		if (element instanceof IResource) {
			return ((IResource)element).getParent();
		} else if (element instanceof SVDBItem) {
			return ((SVDBItem)element).getParent();
		} else {
			return null;
		}
	}

	
	public boolean hasChildren(Object element) {
		if (element instanceof IProjectPathsData) {
			return ((IProjectPathsData)element).hasChildren();
		} else {
			return false;
		}
	}

	
	public Object[] getElements(Object inputElement) {
		return new Object[0];
	}

	
	public void dispose() {
		SVCorePlugin.getDefault().getProjMgr().removeProjectSettingsListener(this);
	}

	
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fViewer = viewer;
	}
	
	public void run() {
		if (!fViewer.getControl().isDisposed()) {
			fLog.debug("Refreshing the project view");
			fViewer.refresh();
		}
	}
}
