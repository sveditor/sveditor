package net.sf.sveditor.ui.wizards.project;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;

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
	
	private Text								fPathEntry;
	private String								fPath;
	private INewFilelistWizardPathValidator		fValidator;
	
	public NewFilelistWizardFirstPage(INewFilelistWizardPathValidator validator) {
		super("New Filelist");
		fValidator = validator;
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
		String msg_warn = null;
		String text = fPathEntry.getText().trim();
	
		Tuple<String, String> vr = null;
		
		if (text.equals("")) {
			msg = "Must specify filename";
		} else if ((vr = fValidator.isValid(text)) != null &&
				(vr.second() != null || vr.first() != null)) {
			// Message already set
			msg = vr.second();
			msg_warn = vr.first();
		} else {
			// See if the extension is ok
			List<String> exts = SVCorePlugin.getDefault().getDefaultArgFileExts();
			int last_dot = text.lastIndexOf('.');
			
			if (last_dot != -1) {
				msg_warn = "filename doesn't have an extension";
			} else {
				String ext = text.substring(last_dot);
				if (!exts.contains(ext)) {
					msg_warn = "extension \"" + ext + "\" is not a recognized filelist extension";
				}
			}
		}
		
		fPath = text;
	
		setMessage(msg_warn, WARNING);
		setErrorMessage(msg);
		setPageComplete((msg == null));
	}
	
}
