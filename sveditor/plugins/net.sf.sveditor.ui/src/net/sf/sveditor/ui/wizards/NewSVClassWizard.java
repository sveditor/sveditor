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


package net.sf.sveditor.ui.wizards;

import net.sf.sveditor.core.srcgen.NewClassGenerator;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;

public class NewSVClassWizard extends AbstractNewSVItemFileWizard {
	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVClassWizard";

	public NewSVClassWizard() {
		super();
	}
	
	
	@Override
	protected AbstractNewSVItemFileWizardPage createPage() {
		return new NewSVClassWizardPage();
	}

	@Override
	protected void generate(IProgressMonitor monitor, IFile file_path) {
		NewClassGenerator gen = new NewClassGenerator();
		
		gen.generate(getIndexIterator(monitor), 
				file_path,
				fPage.getOption(AbstractNewSVItemFileWizardPage.NAME, null),
				fPage.getOption(NewSVClassWizardPage.SUPER_CLASS, null),
				fPage.getOption(NewSVClassWizardPage.OVERRIDE_NEW, "true").equals("true"),
				monitor);
	}

}
