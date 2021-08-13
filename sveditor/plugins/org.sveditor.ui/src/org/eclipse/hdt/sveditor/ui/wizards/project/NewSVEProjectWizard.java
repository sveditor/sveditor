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
package org.eclipse.hdt.sveditor.ui.wizards.project;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.SVProjectNature;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

public class NewSVEProjectWizard extends BasicNewProjectResourceWizard {
	public static final String ID = SVUiPlugin.PLUGIN_ID + ".newSVEProject";
	
	private WizardNewProjectCreationPage		fNameLocationPage;
	private NewSVEProjectFilelistPage			fFilelistPage;

	@Override
	public void addPages() {
		super.addPages();
		
		fNameLocationPage = (WizardNewProjectCreationPage)getPages()[0];
		
		fFilelistPage = new NewSVEProjectFilelistPage(fNameLocationPage);
		addPage(fFilelistPage);
	}

	@Override
	public boolean performFinish() {
		boolean ret = super.performFinish();
		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		
		if (ret) {
			IProject project = getNewProject();
			SVProjectNature.ensureHasSvProjectNature(project);
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = pmgr.getProjectData(project);
			SVProjectFileWrapper fw = new SVProjectFileWrapper();
			
			for (NewSVEProjectFilelistPage.PathInfo pi : fFilelistPage.getPathList()) {
				if (pi.fNewContent != null) {
					// Create 
					String rpath = SVFileUtils.expandVars(pi.fPath, project.getName(), true);
					OutputStream os = fs_provider.openStreamWrite(rpath);
					
					if (os != null) {
						PrintStream ps = new PrintStream(os);
						ps.println(pi.fNewContent);
						ps.flush();
						fs_provider.closeStream(os);
					}
				}
			
				fw.addArgFilePath(pi.fPath);
			}
		
			pdata.setProjectFileWrapper(fw, true);
		}
		
		return ret;
	}

	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		if (ResourcesPlugin.getWorkspace().getRoot().getProjects().length > 0) {
			List<IWizardPage> pl = getPageList();
			int idx = pl.indexOf(page);
		
			// Skip the 'Project Refs' page
			if (idx == 0) {
				idx++;
			}
		
			return (idx+1 < pl.size())?pl.get(idx+1):null;
		} else {
			return super.getNextPage(page);
		}
	}

	@Override
	public IWizardPage getPreviousPage(IWizardPage page) {
		if (ResourcesPlugin.getWorkspace().getRoot().getProjects().length > 0) {
			List<IWizardPage> pl = getPageList();
			int idx = pl.indexOf(page);
		
			// Skip the 'Project Refs' page
			if (idx == 2) {
				idx--;
			}
		
			return (idx-1 >= 0)?pl.get(idx+1):null;
		} else {
			return super.getPreviousPage(page);
		}
	}

	
	private List<IWizardPage> getPageList() {
		List<IWizardPage> ret = new ArrayList<IWizardPage>();
		for (IWizardPage p : getPages()) {
			ret.add(p);
		}
		return ret;
	}

}
