package net.sf.sveditor.svt.editor.wizards;

import net.sf.sveditor.core.SVFileUtils;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewSVTDescriptorPage extends WizardPage {
	
	private Text				fFolderPath;
	private Button				fFolderBrowse;
	private Text				fFilePath;

	private IContainer			fContainer;
	private String				fFilename;
	
	
	public NewSVTDescriptorPage(IContainer container) {
		super("New SV Template Descriptor");
		setTitle("Create a new SystemVerilog Template Descriptor File");
		fContainer = container;
		fFilename = "";
	}
	
	public IContainer getFolder() {
		return fContainer;
	}
	
	public String getFilename() {
		return fFilename;
	}
	
	public void createControl(Composite parent) {
		Composite c = new Composite(parent, SWT.NONE);
		Label l;
		
		c.setLayout(new GridLayout(3, false));
		
		l = new Label(c, SWT.NONE);
		l.setText("Folder:");
		fFolderPath = new Text(c, SWT.SINGLE+SWT.BORDER);
		fFolderPath.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fFolderPath.addModifyListener(modifyListener);
		
		if (fContainer != null) {
			fFolderPath.setText(fContainer.getFullPath().toOSString());
		}
		
		fFolderBrowse = new Button(c, SWT.PUSH);
		fFolderBrowse.setText("Browse...");
		fFolderBrowse.addSelectionListener(selectionListener);
		
		l = new Label(c, SWT.NONE);
		l.setText("Name:");
		fFilePath = new Text(c, SWT.SINGLE+SWT.BORDER);
		fFilePath.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fFilePath.addModifyListener(modifyListener);

		l = new Label(c, SWT.NONE);
		l.setText(".svt");
		
		setControl(c);
		validate();
	}
	
	private void validate() {
		String err = null;
		
		if (fFilename.trim().equals("")) {
			err = setErr(err, "No filename specified");
		}
		
		if (fContainer == null || !fContainer.exists()) {
			err = setErr(err, "Folder path does not exist");
		}
		
		if (fContainer != null && !fFilename.trim().equals("")) {
			IFile file = fContainer.getFile(new Path(fFilename + ".svt"));
			if (file.exists()) {
				err = setErr(err, "File " + fFilename + ".svt exists");
			}
		}
		
		setErrorMessage(err);
	}
	
	private static String setErr(String err, String msg) {
		return (err == null)?msg:err;
	}
	
	private ModifyListener modifyListener = new ModifyListener() {
		public void modifyText(ModifyEvent e) {
			if (e.widget == fFilePath) {
				fFilename = fFilePath.getText();
			} else if (e.widget == fFolderPath) {
				fContainer = SVFileUtils.getWorkspaceFolder(fFolderPath.getText()); 
			}
			validate();
		}
	};

	private SelectionListener selectionListener = new SelectionListener() {
		
		public void widgetSelected(SelectionEvent e) {
			WorkspaceDirectoryDialog dlg = 
					new WorkspaceDirectoryDialog(getShell(), fContainer);
			
			if (dlg.open() == Window.OK) {
				fContainer = dlg.getContainer();
				
				if (fContainer == null) {
					fFolderPath.setText("");
				} else {
					fFolderPath.setText(fContainer.getFullPath().toOSString());
				}
			}
		}
		
		public void widgetDefaultSelected(SelectionEvent e) {}
	};
}
