/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.explorer;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVProjectNature;
import org.eclipse.hdt.sveditor.core.db.project.SVDBPath;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchSite;
import org.eclipse.ui.handlers.HandlerUtil;

public class AddArgFileToProjectHandler extends AbstractHandler implements
		IHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		ISelection sel = HandlerUtil.getCurrentSelection(event);
		IWorkbenchSite site = HandlerUtil.getActiveSite(event);
	
		if (sel instanceof IStructuredSelection) {
			IStructuredSelection sel_s = (IStructuredSelection)sel;
		
			IFile file = null;
			if (sel_s.getFirstElement() instanceof IFile) {
				file = (IFile)sel_s.getFirstElement();
			} else if (sel_s.getFirstElement() instanceof IAdaptable) {
				file = (IFile)((IAdaptable)sel_s.getFirstElement()).getAdapter(IFile.class);
			}
			
			if (file != null) {
				IProject p = file.getProject();
				SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
				SVDBProjectData pdata = pmgr.getProjectData(p);
			
				SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
			
				boolean have = false;
				IPath proj_path = file.getProjectRelativePath();
				for (SVDBPath path : fw.getArgFilePaths()) {
					if (path.getPath().equals("${project_loc}/" + proj_path.toOSString())) {
						have = true;
						break;
					}
				}
				
				IViewSite vsite = (site instanceof IViewSite)?(IViewSite)site:null;
			
				// Ensure the project has the SVE nature added. This is important
				// for the builder to work correctly
				SVProjectNature.ensureHasSvProjectNature(p);
				
				if (!have) {
					fw.addArgFilePath("${project_loc}/" + proj_path.toOSString());
					pdata.setProjectFileWrapper(fw, true);
				
					if (vsite != null) {
						vsite.getActionBars().getStatusLineManager().setMessage(
								"Adding " + proj_path.toOSString() + " to SVE project");
					}
				} else {
					if (vsite != null) {
						vsite.getActionBars().getStatusLineManager().setMessage(
								"" + proj_path.toOSString() + " already added to SVE project");
					}
				}
			}
		}

		return null;
	}

}
