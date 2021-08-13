/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.script.launch;

import java.io.File;

import org.eclipse.hdt.sveditor.ui.WorkspaceDirectoryDialog;
import org.eclipse.hdt.sveditor.ui.WorkspaceFileDialog;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.script.launch.BuildScriptLauncherConstants;
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

public class ScriptLauncherScriptTab extends AbstractLaunchConfigurationTab implements BuildScriptLauncherConstants {

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
	
	public ScriptLauncherScriptTab() {
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd;
		
		Composite top = new Composite(parent, SWT.NONE);
		top.setLayout(new GridLayout());
		top.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Group script_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		script_group.setText("Scri&pt Name");
		script_group.setLayout(new GridLayout(2, false));
		script_group.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		
		fScriptText = new Text(script_group, SWT.SINGLE+SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fScriptText.setLayoutData(gd);
		fScriptText.addModifyListener(modifyListener);
		
		fScriptBrowseWS = new Button(script_group, SWT.PUSH);
		fScriptBrowseWS.setText("&Browse Workspace...");
		fScriptBrowseWS.addSelectionListener(scrSelectionListener);
		
		fScriptBrowseFS = new Button(script_group, SWT.PUSH);
		fScriptBrowseFS.setText("Browse &Filesystem...");
		fScriptBrowseFS.addSelectionListener(scrSelectionListener);
	
		// Working Directory Group
		Group wd_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		wd_group.setText("W&orking Directory");
		wd_group.setLayout(new GridLayout(2, false));
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		wd_group.setLayoutData(gd);
		
		fWorkingDirText = new Text(wd_group, SWT.SINGLE+SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fWorkingDirText.setLayoutData(gd);
		fWorkingDirText.addModifyListener(modifyListener);
		
		fWorkingDirBrowseWS = new Button(wd_group, SWT.PUSH);
		fWorkingDirBrowseWS.setText("B&rowse Workspace...");
		fWorkingDirBrowseWS.addSelectionListener(wdSelectionListener);
		
		fWorkingDirBrowseFS = new Button(wd_group, SWT.PUSH);
		fWorkingDirBrowseFS.setText("Browse F&ilesystem...");
		fWorkingDirBrowseFS.addSelectionListener(wdSelectionListener);
		
		// Script Arguments
		Group args_group = new Group(top, SWT.SHADOW_ETCHED_IN);
		args_group.setText("Co&mmand line");
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
		return "&Script";
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
		scr = SVFileUtils.expandVars(scr, null, false);
		
		if (scr.trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a script");
			}
		} else {
			File script_f = SVFileUtils.getFile(scr.trim());
			
			if (!script_f.isFile()) {
				if (getErrorMessage() == null) {
					setErrorMessage("Script " + scr + " does not exist");
				}
			}
		}

		String wd = fWorkingDirText.getText();
		wd = SVFileUtils.expandVars(wd, null, false);
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
			
			if (src == fWorkingDirText) {
				fWorkingDir = fWorkingDirText.getText().trim();
			} else if (src == fArgumentsText) {
				fArguments = fArgumentsText.getText();
			} else if (src == fScriptText) {
				fScript = fScriptText.getText();
			}
		
			setDirty(true);
			updateLaunchConfigurationDialog();
		}
	};
	
	private SelectionListener			wdSelectionListener = new SelectionListener() {
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (e.getSource() == fWorkingDirBrowseWS) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(fWorkingDirBrowseWS.getShell(), "Select Working Directory");
				if (dlg.open() == Window.OK) {
					fWorkingDirText.setText("${workspace_loc}" + dlg.getPath());
				}
			} else if (e.getSource() == fWorkingDirBrowseFS) {
				DirectoryDialog dlg = new DirectoryDialog(fWorkingDirBrowseFS.getShell());
				dlg.setText("Select Working Directory");
				
				String path = dlg.open();
				
				if (path != null && !path.trim().equals("")) {
					fWorkingDirText.setText(path);
				}
			}
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) { }
	};
	
	private SelectionListener			scrSelectionListener = new SelectionListener() {
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (e.getSource() == fScriptBrowseWS) {
				WorkspaceFileDialog dlg = new WorkspaceFileDialog(fScriptBrowseWS.getShell(), "Select Script");
				if (dlg.open() == Window.OK) {
					fScriptText.setText("${workspace_loc}" + dlg.getPath());
				}
			} else if (e.getSource() == fScriptBrowseFS) {
				FileDialog dlg = new FileDialog(fScriptBrowseFS.getShell());
				dlg.setText("Select Script");
				
				String path = dlg.open();
				
				if (path != null && !path.trim().equals("")) {
					fScriptText.setText(path);
				}
			}
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) { }
	};	

}
