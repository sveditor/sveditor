package net.sf.sveditor.ui.wizards.imp.compilation.args;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IImportWizard;
import org.eclipse.ui.IWorkbench;

public class CompilationArgImportWizard extends Wizard implements IImportWizard {

	public CompilationArgImportWizard() {
		// TODO Auto-generated constructor stub
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public void addPages() {
		super.addPages();
		addPage(new CompilationArgImportSrcInfoPage());
	}

	@Override
	public boolean performFinish() {
		// TODO Auto-generated method stub
		return false;
	}

}
