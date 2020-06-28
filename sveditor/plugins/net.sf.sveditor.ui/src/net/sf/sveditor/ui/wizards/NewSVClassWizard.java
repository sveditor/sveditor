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


package net.sf.sveditor.ui.wizards;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.srcgen.NewClassGenerator;
import net.sf.sveditor.ui.SVUiPlugin;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
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
		SubMonitor subMonitor = SubMonitor.convert(monitor, 2);
		
		gen.generate(getIndexIterator(subMonitor.newChild(1)), 
				file_path,
				fPage.getOption(AbstractNewSVItemFileWizardPage.NAME, null),
				fPage.getOption(NewSVClassWizardPage.SUPER_CLASS, null),
				fPage.getOption(NewSVClassWizardPage.OVERRIDE_NEW, "true").equals("true"),
				subMonitor.newChild(1));
		
		if (getOption(NewSVClassWizardPage.ADD_TO_PACKAGE, "false").equals("true")) {
			// Update package source
			SVDBPackageDecl pkg = fAddToPackagePage.getPackage();
			ISVDBIndex pkg_index = fAddToPackagePage.getPackageIndex();
			String pkg_file = fAddToPackagePage.getPackageFile();
			InputStream pkg_in = pkg_index.getFileSystemProvider().openStream(pkg_file);
			List<String> pkg_content = SVFileUtils.readInputLines(pkg_in);
			pkg_index.getFileSystemProvider().closeStream(pkg_in);
			
			OutputStream pkg_out = pkg_index.getFileSystemProvider().openStreamWrite(pkg_file);
//			ByteArrayOutputStream pkg_out = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(pkg_out);
			
			int pkg_start = SVDBLocation.unpackLineno(pkg.getLocation());
			int pkg_end = SVDBLocation.unpackLineno(pkg.getEndLocation());
			
			// Now, iterate through the original package content

			// Append lines before the target package
			for (int i=0; i<pkg_start-1; i++) {
				ps.println(pkg_content.get(i));
			}
			
			ps.print(fAddToPackagePage.getContent());
			
			for (int i=pkg_end; i<pkg_content.size(); i++) {
				ps.println(pkg_content.get(i));
			}
		
//			System.out.println("New Package:\n" + pkg_out.toString());
		
			ps.flush();
			pkg_index.getFileSystemProvider().closeStream(pkg_out);
			
		}
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
