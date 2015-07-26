package net.sf.sveditor.ui.wizards.project;

import java.util.Set;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewFilelistWizardFirstPage extends WizardPage {
	
	private Text					fPathEntry;
	private String					fPath;
	private Set<String>				fExistingPaths;
	
	public NewFilelistWizardFirstPage(Set<String> existing_paths) {
		super("New Filelist");
		fExistingPaths = existing_paths;
		setTitle("Specify Filelist Name");
	}
	
	public String getPath() {
		return fPath;
	}

	@Override
	public void createControl(Composite parent) {
		
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout(2, false));
		
		Label l = new Label(c, SWT.NONE);
		l.setText("Path:");
		l.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		
		fPathEntry = new Text(c, SWT.SINGLE);
		fPathEntry.setLayoutData(new GridData(SWT.FILL, SWT.TOP, true, true));
		fPathEntry.setText("sve.f");
		fPathEntry.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				validate();
			}
		});
	
//		fBrowse = new Button(c, SWT.PUSH);
//		fBrowse.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
//		fBrowse.setText("Browse...");
		
		validate();

		setControl(c);
	}
	
	private void validate() {
		String msg = null;
		String text = fPathEntry.getText().trim();
		
		if (text.equals("")) {
			msg = "Must specify filename";
		} else if (fExistingPaths.contains(text)) {
			msg = "Argument file already exists";
		} else {
			// See if the extension is ok
		}
		
		fPath = text;
	
		setErrorMessage(msg);
	}
	
}
