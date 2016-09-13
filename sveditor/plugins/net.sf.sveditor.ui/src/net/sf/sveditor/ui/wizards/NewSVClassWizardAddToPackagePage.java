package net.sf.sveditor.ui.wizards;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBUtil;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.ui.sv.viewer.SystemVerilogInsertLineViewer;
import net.sf.sveditor.ui.sv.viewer.SystemVerilogViewer;

public class NewSVClassWizardAddToPackagePage extends WizardPage {
	private AbstractNewSVItemFileWizard			fParent;
	private SystemVerilogInsertLineViewer		fSvViewer;
	
	public NewSVClassWizardAddToPackagePage(AbstractNewSVItemFileWizard parent) {
		super("Add to Package",
				"Add to Package", null);
//				"Specify where to add the new file in the target package");
		fParent = parent;
		setErrorMessage("Incomplete Page");
	}
	

	@Override
	public void createControl(Composite parent) {
		fSvViewer = new SystemVerilogInsertLineViewer(parent, 
				SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		fSvViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fSvViewer.setContent(
				"\n" +
				"package foo;\n" +
				"	`include \"foo_c1.svh\"\n" +
				"	`include \"foo_c2.svh\"\n" +
				"endpackage\n"
				);
		
		fSvViewer.setLine("`include \"my_c.svh\"", 0);
		
		setControl(fSvViewer.getControl());
	}
	
	@Override
	public void setVisible(boolean visible) {
		super.setVisible(visible);
		
		if (visible) {
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
			
			ISVDBDeclCache cache = pkg_decl.getParent();
			
			System.out.println("pkg: " + pkg_decl.getFilename() + " " + 
					SVDBLocation.unpackLineno(pkg.getLocation()) + ".." + 
					SVDBLocation.unpackLineno(pkg.getEndLocation()));
	
			// Need to obtain the content
			SVDBIndexCollection index_c = fParent.getIndexCollection();
			
			List<ISVDBIndex> index_l = index_c.findManagingIndex(pkg_decl.getFilename());
			
			if (index_l.size() == 0) {
				System.out.println("Failed to find the managing index for pkg " + pkg_decl.getName());
				return;
			}
			
			ISVDBIndex target_index = index_l.get(0);
			
			InputStream in = target_index.getFileSystemProvider().openStream(pkg_decl.getFilename());
			
			String full_content = SVFileUtils.readInput(in);
			target_index.getFileSystemProvider().closeStream(in);

			// Set the content
			fSvViewer.setContent(full_content);
		}
	}


	@Override
	public boolean isPageComplete() {
		return false;
	}
	
}
