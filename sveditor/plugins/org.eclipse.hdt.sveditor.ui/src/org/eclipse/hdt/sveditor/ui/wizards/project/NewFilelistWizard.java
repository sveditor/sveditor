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

import java.io.File;

import org.eclipse.hdt.sveditor.ui.content_providers.SVDBFileSystemContentProvider;
import org.eclipse.hdt.sveditor.ui.content_providers.SVDBFileSystemLabelProvider;
import org.eclipse.hdt.sveditor.ui.wizards.new_filelist.NewFileListWizardAddFilesPage;

import org.eclipse.hdt.sveditor.core.db.index.SVDBScopedFileSystemProvider;
import org.eclipse.jface.wizard.Wizard;

public class NewFilelistWizard extends Wizard {
	private NewFilelistWizardFirstPage			fNamePage;
	private NewFileListWizardAddFilesPage		fAddFilesPage;
	private File								fRoot;
	private String								fProjectName;
	private INewFilelistWizardPathValidator		fValidator;
	
	public NewFilelistWizard(
			File 								root, 
			String								pname,
			INewFilelistWizardPathValidator		validator) {
		fRoot = root;
		fProjectName = pname;
		fValidator = validator;
	}
	
	@Override
	public void addPages() {
		fNamePage = new NewFilelistWizardFirstPage(fValidator);
		addPage(fNamePage);

		SVDBScopedFileSystemProvider fs_provider = new SVDBScopedFileSystemProvider();
		fs_provider.init(fRoot.getAbsolutePath(), fProjectName);
		
		fAddFilesPage = new NewFileListWizardAddFilesPage(
				new SVDBFileSystemContentProvider(),
				new SVDBFileSystemLabelProvider(fs_provider),
				fs_provider,
				fs_provider);
		fAddFilesPage.setRequireFiles(false);
	
		// The path used by AddFilesPage is /<project_name>
		fAddFilesPage.setPrefix("./", 
				fProjectName.length()+2);
		addPage(fAddFilesPage);
	}
	
	public String getArgFileContent() {
		return fAddFilesPage.getArgFileContent();
	}
	
	public String getPath() {
		return fNamePage.getPath();
	}


	@Override
	public boolean performFinish() {
		return true;
	}

}
