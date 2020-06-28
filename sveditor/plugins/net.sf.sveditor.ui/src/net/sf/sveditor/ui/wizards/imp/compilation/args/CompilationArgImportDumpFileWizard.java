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
package net.sf.sveditor.ui.wizards.imp.compilation.args;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IImportWizard;
import org.eclipse.ui.IWorkbench;

public class CompilationArgImportDumpFileWizard extends Wizard implements IImportWizard {
	private CompilationArgImportDumpFileSrcInfoPage			fSrcInfoPage;
	private CompilationArgImportOutPage						fOutPage;
	private IStructuredSelection							fSel;

	public CompilationArgImportDumpFileWizard() {
		// TODO Auto-generated constructor stub
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		fSel = selection;
	}
	
	@Override
	public void addPages() {
		super.addPages();
		fSrcInfoPage = new CompilationArgImportDumpFileSrcInfoPage();
		fOutPage = new CompilationArgImportOutPage();
		
		addPage(fSrcInfoPage);
		addPage(fOutPage);
		
		IContainer init_scope = null;
		if (fSel != null && !fSel.isEmpty()) {
			Object first = fSel.getFirstElement();
			
			if (first instanceof IContainer) {
				init_scope = (IContainer)first;
			} else if (first instanceof IFile) {
				init_scope = ((IFile)first).getParent();
			}
		}
		
		if (init_scope != null) {
			fSrcInfoPage.setSrcDir("${workspace_loc}" + init_scope.getFullPath());
			fSrcInfoPage.setDestDir("" + init_scope.getFullPath());
		}
	}
	
	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		IWizardPage next = super.getNextPage(page);
		
		if (next == fOutPage) {
			// Propagate the content
			fOutPage.setSrcText(fSrcInfoPage.getCapturedArgs());
		}
		
		return next;
	}
	
	@Override
	public boolean performFinish() {
		String content = fOutPage.getResultText();
		String dest_dir = fSrcInfoPage.getDestDir();
		String dest_file = fSrcInfoPage.getDestFile();
		
		IFile file = SVFileUtils.getWorkspaceFile(dest_dir + "/" + dest_file);
		SVFileUtils.copy(content, file);
		
		if (fSrcInfoPage.getAddToProject()) {
			String newpath = "${workspace_loc}" + file.getFullPath();

			// Add the new file to the project settings
			IProject p = file.getProject();
			
			// Ensure the project is setup as SVE project
			SVProjectNature.ensureHasSvProjectNature(p);
			
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = pmgr.getProjectData(p);
			
			SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
			List<SVDBPath> paths = fw.getArgFilePaths();
			boolean already_added = false;
			
			for (SVDBPath path : paths) {
				if (path.getPath().equals(newpath)) {
					already_added = true;
					break;
				}
			}
			
			if (!already_added) {
				paths.add(new SVDBPath(newpath));
				pdata.setProjectFileWrapper(fw, true);
			}
		}

		return true;
	}

}
