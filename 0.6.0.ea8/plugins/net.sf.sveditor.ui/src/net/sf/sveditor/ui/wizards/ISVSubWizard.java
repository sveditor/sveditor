package net.sf.sveditor.ui.wizards;

import java.util.Map;

import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.IWizardPage;

public interface ISVSubWizard {
	
	void init(IWizard wizard, Map<String, Object> options);

	IWizardPage getNextPage(IWizardPage page);
	
	IWizardPage getPreviousPage(IWizardPage page);
	
	boolean canFinish();

}
