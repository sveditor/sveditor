package net.sf.sveditor.ui.wizards.imp.compilation.args;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;

public class CompilationArgImportOutPage extends WizardPage {
	
	private String					fSrcText;
	
	private Text					fResultText;
	private String					fResult;
	
	public CompilationArgImportOutPage() {
		super("Output Settings");
	}
	
	public void setSrcText(String text) {
		fSrcText = text;
		
		if (fResultText != null) {
			updateResultText();
		}
	}

	public void createControl(Composite parent) {
		SashForm sash = new SashForm(parent, SWT.VERTICAL);
		sash.setLayout(new GridLayout());
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		Composite top = new Composite(sash, SWT.BORDER);
		
//		Composite middle = new Composite(sash, SWT.BORDER);
		
		Composite bottom = new Composite(sash, SWT.BORDER);
		bottom.setLayout(new GridLayout());
		bottom.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fResultText = new Text(bottom, 
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);

		setControl(sash);
	}
	
	private void updateResultText() {
		// TODO: Apply filter
		
		fResult = fSrcText;
		fResultText.setText(fResult);
	}

}
