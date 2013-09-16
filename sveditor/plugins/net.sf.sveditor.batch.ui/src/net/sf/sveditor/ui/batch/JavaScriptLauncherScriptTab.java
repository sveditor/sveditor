package net.sf.sveditor.ui.batch;

import java.io.File;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;
import net.sf.sveditor.ui.WorkspaceFileDialog;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;

public class JavaScriptLauncherScriptTab extends AbstractLaunchConfigurationTab implements JavaScriptLauncherConstants {
	
	private String								fScript;
	private Text								fScriptText;
	
	private Button								fScriptBrowseWS;
	private Button								fScriptBrowseFS;
	
	private String								fWorkingDir;
	private Text								fWorkingDirText;
	
	private Button								fWorkingDirBrowseWS;
	private Button								fWorkingDirBrowseFS;
	
	private Text								fArgumentsText;
	private String								fArguments;
	
	public JavaScriptLauncherScriptTab() {
		fScript = "";
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd;
		
		Composite top = new Composite(parent, SWT.NONE);
		top.setLayout(new GridLayout());
		top.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
	
		// Script Group
		Group script_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		script_group.setText("JavaScript");
		script_group.setLayout(new GridLayout(2, false));
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		script_group.setLayoutData(gd);
		
		fScriptText = new Text(script_group, SWT.SINGLE+SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fScriptText.setLayoutData(gd);
		fScriptText.addModifyListener(modifyListener);
		
		fScriptBrowseWS = new Button(script_group, SWT.PUSH);
		fScriptBrowseWS.setText("Browse Workspace...");
		fScriptBrowseWS.addSelectionListener(selectionListener);
		
		fScriptBrowseFS = new Button(script_group, SWT.PUSH);
		fScriptBrowseFS.setText("Browse Filesystem...");
		fScriptBrowseFS.addSelectionListener(selectionListener);
	
		// Working Directory Group
		Group wd_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		wd_group.setText("Working Directory");
		wd_group.setLayout(new GridLayout(2, false));
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		wd_group.setLayoutData(gd);
		
		fWorkingDirText = new Text(wd_group, SWT.SINGLE+SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fWorkingDirText.setLayoutData(gd);
		fWorkingDirText.addModifyListener(modifyListener);
		
		fWorkingDirBrowseWS = new Button(wd_group, SWT.PUSH);
		fWorkingDirBrowseWS.setText("Browse Workspace...");
		fWorkingDirBrowseWS.addSelectionListener(selectionListener);
		
		fWorkingDirBrowseFS = new Button(wd_group, SWT.PUSH);
		fWorkingDirBrowseFS.setText("Browse Filesystem...");
		fWorkingDirBrowseFS.addSelectionListener(selectionListener);
		
		// Script Arguments
		Group args_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		args_group.setText("Arguments");
		args_group.setLayout(new GridLayout());
		args_group.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fArgumentsText = new Text(args_group, SWT.MULTI+SWT.BORDER);
		fArgumentsText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fArgumentsText.addModifyListener(modifyListener);
		
		
		setControl(top);
	}

	@Override
	public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
		configuration.setAttribute(SCRIPT_LIST, "");
		configuration.setAttribute(WORKING_DIR, System.getProperty("user.dir"));
		configuration.setAttribute(ARGUMENTS, "");
	}

	@Override
	public void initializeFrom(ILaunchConfiguration configuration) {
		try {
			fScript = configuration.getAttribute(SCRIPT_LIST, "");
			fScriptText.setText(fScript);
			
			fWorkingDir = configuration.getAttribute(WORKING_DIR, System.getProperty("user.dir"));
			fWorkingDirText.setText(fWorkingDir);
			
			fArguments = configuration.getAttribute(ARGUMENTS, "");
			fArgumentsText.setText(fArguments);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void performApply(ILaunchConfigurationWorkingCopy configuration) {
		configuration.setAttribute(SCRIPT_LIST, fScript);
		configuration.setAttribute(WORKING_DIR, fWorkingDir);
		configuration.setAttribute(ARGUMENTS, fArguments);
	}

	@Override
	public String getName() {
		return "Script";
	}
	
	@Override
	public boolean canSave() {
		return super.canSave();
	}

	@Override
	public boolean isValid(ILaunchConfiguration launchConfig) {
		setErrorMessage(null);
		setMessage(null);
		
		String scr = fScriptText.getText();
		
		if (scr.trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a script to execute");
			}
		} else {
			if (scr.startsWith("${workspace_loc}")) {
				String ws_path = scr.substring("${workspace_loc}".length());
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
				try {
					IFile scr_f = root.getFile(new Path(ws_path));
					
					if (!scr_f.exists()) {
						if (getErrorMessage() == null) {
							setErrorMessage("Script file " + scr + " does not exist");
						}
					}
				} catch (Exception e) {
					if (getErrorMessage() == null) {
						setErrorMessage("Script file " + scr + " does not exist");
					}
				}
				
			} else {
				File file = new File(scr);
				
				if (!file.exists() && getErrorMessage() == null) {
					setErrorMessage("Script file does not exist");
				}
			}
		}
		
		String wd = fWorkingDirText.getText();
		if (wd.trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a working directory");
			}
		} else {
			File wd_f = SVFileUtils.getFile(wd.trim());
			
			if (!wd_f.isDirectory()) {
				if (getErrorMessage() == null) {
					setErrorMessage("Working directory " + wd + " does not exist");
				}
			}
		}
		
		return (getErrorMessage() == null && getMessage() == null);
	}

	private ModifyListener				modifyListener = new ModifyListener() {
		
		@Override
		public void modifyText(ModifyEvent e) {
			Object src = e.getSource();
			
			if (src == fScriptText) {
				fScript = fScriptText.getText().trim();
			} else if (src == fWorkingDirText) {
				fWorkingDir = fWorkingDirText.getText().trim();
			} else if (src == fArgumentsText) {
				fArguments = fArgumentsText.getText();
			}
		
			setDirty(true);
			updateLaunchConfigurationDialog();
		}
	};
	
	private SelectionListener			selectionListener = new SelectionListener() {
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (e.getSource() == fScriptBrowseWS) {
				WorkspaceFileDialog dlg = new WorkspaceFileDialog(fScriptBrowseWS.getShell());
				if (dlg.open() == Window.OK) {
					fScriptText.setText("${workspace_loc}" + dlg.getPath());
				}
			} else if (e.getSource() == fScriptBrowseFS) {
				FileDialog dlg = new FileDialog(fScriptBrowseFS.getShell());
				
				String path = dlg.open();
				
				if (path != null && !path.trim().equals("")) {
					fScriptText.setText(path);
				}
			} else if (e.getSource() == fWorkingDirBrowseWS) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(fWorkingDirBrowseWS.getShell());
				if (dlg.open() == Window.OK) {
					fWorkingDirText.setText("${workspace_loc}" + dlg.getPath());
				}
			} else if (e.getSource() == fWorkingDirBrowseFS) {
				DirectoryDialog dlg = new DirectoryDialog(fWorkingDirBrowseFS.getShell());
				
				String path = dlg.open();
				
				if (path != null && !path.trim().equals("")) {
					fWorkingDirText.setText(path);
				}
			}
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) { }
	};

}
