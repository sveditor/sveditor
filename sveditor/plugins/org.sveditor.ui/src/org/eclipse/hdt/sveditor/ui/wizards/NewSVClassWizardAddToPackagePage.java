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
package org.sveditor.ui.wizards;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBPackageDecl;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.index.SVDBIndexCollection;
import org.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationPainter;
import org.eclipse.jface.text.source.IAnnotationAccess;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;

import org.sveditor.ui.sv.viewer.SystemVerilogInsertLineViewer;

public class NewSVClassWizardAddToPackagePage extends WizardPage {
	private NewSVClassWizard					fParent;
	private SystemVerilogInsertLineViewer		fSvViewer;
	private String								fContent;
	private SVDBPackageDecl						fPackage;
	private String								fPackageFile;
	private ISVDBIndex							fPackageIndex;
	
	public NewSVClassWizardAddToPackagePage(NewSVClassWizard parent) {
		super("Add to Package",
				"Add to Package", null);
		fParent = parent;
		setErrorMessage(null);
	}
	
	public String getContent() {
		return fContent;
	}
	
	public SVDBPackageDecl getPackage() {
		return fPackage;
	}
	
	public String getPackageFile() {
		return fPackageFile;
	}
	
	public ISVDBIndex getPackageIndex() {
		return fPackageIndex;
	}
	

	@Override
	public void createControl(Composite parent) {
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		fSvViewer = new SystemVerilogInsertLineViewer(c, 
				SWT.V_SCROLL+SWT.H_SCROLL);
		fSvViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fContent = "";
	
		fSvViewer.getSvViewer().getDocument().addDocumentListener(
				new IDocumentListener() {
					
					@Override
					public void documentChanged(DocumentEvent event) {
						fContent = fSvViewer.getSvViewer().getDocument().get();
					}
					
					@Override
					public void documentAboutToBeChanged(DocumentEvent event) { }
				});
		
		setControl(c);
	}
	
	private void updateContent() {
		ISVDBIndexIterator index_it = fParent.getIndexIterator(new NullProgressMonitor());
		String pkg_name = fParent.fPage.getOption(NewSVClassWizardPage.PACKAGE, "UNKNOWN");
		
		// Lookup the actual package
		List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), pkg_name,
				new SVDBFindByNameMatcher(SVDBItemType.PackageDecl));
		
		if (result.size() == 0) {
			setErrorMessage("Internal Error: Failed to find package \"" + pkg_name + "\"");
			return;
		}
	
		SVDBDeclCacheItem pkg_decl = result.get(0);
		SVDBPackageDecl pkg = (SVDBPackageDecl)pkg_decl.getSVDBItem();
		fPackage = pkg;
		
		// Need to obtain the content
		SVDBIndexCollection index_c = fParent.getIndexCollection();
		
		List<ISVDBIndex> index_l = index_c.findManagingIndex(pkg_decl.getFilename());
		
		if (index_l.size() == 0) {
			System.out.println("Failed to find the managing index for pkg " + pkg_decl.getName());
			return;
		}
		
		fPackageIndex = index_l.get(0);
	
		fPackageFile = pkg_decl.getFilename();
		InputStream in = fPackageIndex.getFileSystemProvider().openStream(fPackageFile);
		
		String full_content = SVFileUtils.readInput(in);
		fPackageIndex.getFileSystemProvider().closeStream(in);
		
		StringBuilder trimmed_content = new StringBuilder();
		int lineno=1;
		int pos=0;
		int start_line = SVDBLocation.unpackLineno(pkg.getLocation());
		int end_line   = SVDBLocation.unpackLineno(pkg.getEndLocation());
		int pkg_lines=0;
		
		do {
			int eol = full_content.indexOf('\n', pos);
			
			if (eol < 0) {
				if (lineno >= start_line && lineno <= end_line) {
					trimmed_content.append(full_content.substring(pos));
					pkg_lines++;
				}
				break;
			} else {
				if (lineno >= start_line && lineno <= end_line) {
					trimmed_content.append(full_content.substring(pos, eol+1));
					pkg_lines++;
				}
			}
		
			lineno++;
			pos = eol+1;
		} while (true);

		// Set the content
		fSvViewer.setContent(trimmed_content.toString());
		fSvViewer.setInsertRange(1, pkg_lines);
		
		String filename = fParent.getOption(NewSVClassWizardPage.FILE_NAME, "");
		fSvViewer.setLine("`include \"" + filename + "\"", pkg_lines-1);
	}
	
	@Override
	public void setVisible(boolean visible) {
		super.setVisible(visible);
		
		if (visible) {
			updateContent();
		}
	}


	@Override
	public boolean isPageComplete() {
		return true;
	}
	
}
