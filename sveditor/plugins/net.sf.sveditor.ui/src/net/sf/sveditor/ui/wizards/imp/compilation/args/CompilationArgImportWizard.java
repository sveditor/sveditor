package net.sf.sveditor.ui.wizards.imp.compilation.args;

import net.sf.sveditor.core.SVFileUtils;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IImportWizard;
import org.eclipse.ui.IWorkbench;

public class CompilationArgImportWizard extends Wizard implements IImportWizard {
	private CompilationArgImportSrcInfoPage			fSrcInfoPage;
	private CompilationArgImportOutPage				fOutPage;
	private IStructuredSelection					fSel;

	public CompilationArgImportWizard() {
		// TODO Auto-generated constructor stub
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		fSel = selection;
	}
	
	@Override
	public void addPages() {
		super.addPages();
		fSrcInfoPage = new CompilationArgImportSrcInfoPage();
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

		return true;
	}

}
