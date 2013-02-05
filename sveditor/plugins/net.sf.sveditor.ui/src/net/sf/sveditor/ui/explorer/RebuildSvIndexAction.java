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
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.actions.SelectionListenerAction;
import org.eclipse.ui.navigator.CommonActionProvider;
import org.eclipse.ui.navigator.ICommonMenuConstants;

public class RebuildSvIndexAction extends CommonActionProvider implements ILogLevel {

	public RebuildSvIndexAction() {
		fRebuildAction = new RebuildIndexAction();
	}
	
	public void fillContextMenu(IMenuManager menu) {
		menu.insertAfter(ICommonMenuConstants.GROUP_ADDITIONS, fRebuildAction);
	}
	
	private RebuildIndexAction			fRebuildAction;
	
	private class RebuildIndexAction extends SelectionListenerAction {
		private LogHandle					fLog;
		
		public RebuildIndexAction() {
			super("Rebuild SV Index");
			fLog = LogFactory.getLogHandle("RebuildIndexAction");
		}
		
		public void run() {
			
			IStructuredSelection sel_s = (IStructuredSelection)
				getActionSite().getViewSite().getSelectionProvider().getSelection();
			updateSelection(sel_s);

			List<IProject> projects = new ArrayList<IProject>();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();

			for (Object sel_o : sel_s.toList()) {
				IProject p = null;
				if (sel_o instanceof IProject) {
					p = (IProject)sel_o;
				} else if (sel_o instanceof IResource) {
					p = ((IResource)sel_o).getProject();
				}
				
				if (p != null && !projects.contains(p)) {
					projects.add(p);
				}
			}
			
			for (IProject p : projects) {
				fLog.debug(LEVEL_MIN, "Rebuild index for project \"" + p.getName() + "\"");
				try {
					p.deleteMarkers(IMarker.PROBLEM, true, IResource.DEPTH_INFINITE);
				} catch (CoreException e) {}
			
				SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
				SVDBProjectData pd = pmgr.getProjectData(p);
			
				SVDBIndexCollection ic = pd.getProjectIndexMgr();
//				List<ISVDBIndex> index_list = rgy.getProjectIndexList(p.getName());
				List<ISVDBIndex> index_list = ic.getIndexList();
				
				for (ISVDBIndex index : index_list) {
					fLog.debug(LEVEL_MIN, "  Rebuild index " + index.getBaseLocation());
				}

				/*
				for (ISVDBIndex index : index_list) {
					fLog.debug(LEVEL_MIN, "rebuildIndex " + index.getBaseLocation());
					index.rebuildIndex();
				}
				 */
				SVUiPlugin.getDefault().refreshIndexList(index_list);
			}
			
			// Finally, rebuild global index
			rgy.rebuildIndex(new NullProgressMonitor(), SVDBIndexRegistry.GLOBAL_PROJECT);
		}
	}

}
