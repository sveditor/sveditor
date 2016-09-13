/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.wizards;

import net.sf.sveditor.core.srcgen.NewClassGenerator;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.wizard.IWizardPage;

public class NewSVClassWizard extends AbstractNewSVItemFileWizard {
	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVClassWizard";
	protected NewSVClassWizardAddToPackagePage	fAddToPackagePage;

	public NewSVClassWizard() {
		super();
	}
	
	
	@Override
	protected AbstractNewSVItemFileWizardPage createPage() {
		return new NewSVClassWizardPage(this);
	}
	
	@Override
	public void addPages() {
		// TODO Auto-generated method stub
		super.addPages();
		fAddToPackagePage = new NewSVClassWizardAddToPackagePage(this);
		addPage(fAddToPackagePage);
	}

	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		if (page == fPage && 
				fPage.getOption(NewSVClassWizardPage.ADD_TO_PACKAGE, "false").equals("true")) {
			return fAddToPackagePage;
		}
		return null;
	}

	@Override
	public IWizardPage getPreviousPage(IWizardPage page) {
		if (page == fAddToPackagePage) {
			return fPage;
		}
		return null;
	}


	@Override
	protected void generate(IProgressMonitor monitor, IFile file_path) {
		NewClassGenerator gen = new NewClassGenerator(fTagProc);
		
		gen.generate(getIndexIterator(monitor), 
				file_path,
				fPage.getOption(AbstractNewSVItemFileWizardPage.NAME, null),
				fPage.getOption(NewSVClassWizardPage.SUPER_CLASS, null),
				fPage.getOption(NewSVClassWizardPage.OVERRIDE_NEW, "true").equals("true"),
				monitor);
	}

	@Override
	public boolean canFinish() {
		if (fPage.getOption(NewSVClassWizardPage.ADD_TO_PACKAGE, "false").equals("true")) {
			return fAddToPackagePage.isPageComplete();
		} else {
			return fPage.isPageComplete();
		}
	}
	
	

}
