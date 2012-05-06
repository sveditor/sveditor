package net.sf.sveditor.ui.wizards.templates;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;

public class ClassBrowseDialog extends Dialog {
	
	public ClassBrowseDialog(Shell parent) {
		super(parent);
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		Button b = new Button(parent, SWT.PUSH);
		b.setText("B");
		
		return b;
	}
	
}
