/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.ui.prop_pages;

import org.sveditor.ui.WorkspaceFileDialog;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.Dialog;
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
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

public class AddFilePathDialog extends Dialog {
	private Text				fPath;
	private String				fPathStr;
	private IProject			fProject;
	private String				fTitle;
	
	public AddFilePathDialog(Shell shell, IProject p, String title) {
		super(shell);
		fProject = p;
		fTitle = title;
	}
	
	public void setInitialPath(String path) {
		fPathStr = path;
	}
	
	public void configureShell (Shell shell) {
		super.configureShell(shell);
		shell.setText(fTitle);
	}

	public String getPath() {
		return fPathStr;
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(2, false));
		
		GridData gd;
		
		fPath = new Text(frame, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.widthHint = 250;
		fPath.setLayoutData(gd);
		fPath.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fPathStr = fPath.getText();
			}
		});
		
		if (fPathStr != null) {
			fPath.setText(fPathStr);
		}

		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayout(new GridLayout(1, true));
		button_bar.setLayoutData(new GridData(SWT.CENTER, SWT.FILL, false, true));

		Button add_proj_path = new Button(button_bar, SWT.PUSH);
		add_proj_path.setText("Add &Project Path");
		add_proj_path.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		add_proj_path.addSelectionListener(new SelectionListener() {

			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				ProjectFileDialog dlg = new ProjectFileDialog(getShell(), fProject);
				if (dlg.open() == Window.OK) {
					if (dlg.getPath() != null) {
						IPath proj_loc = new Path("${project_loc}") ;
						IPath path = new Path(dlg.getPath()) ;
						fPath.setText(proj_loc.append(path.removeFirstSegments(1)).toString()) ;
					}
				}
			}
		});

		Button add_ws_path = new Button(button_bar, SWT.PUSH);
		add_ws_path.setText("Add &Workspace Path");
		add_ws_path.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		add_ws_path.addSelectionListener(new SelectionListener() {

			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				WorkspaceFileDialog dlg = new WorkspaceFileDialog(getShell());
				getShell().setText("Select a File");
				
				if (dlg.open() == Window.OK) {
					if (dlg.getPath() != null) {
						fPath.setText("${workspace_loc}" + dlg.getPath());
					}
				}
			}
		});
		
		Button add_fs_path = new Button(button_bar, SWT.PUSH);
		add_fs_path.setText("Add &Filesystem Path");
		add_fs_path.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		add_fs_path.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				FileDialog dlg = new FileDialog(getShell());
				dlg.setText("Select a File");
				
				String result = dlg.open();
				
				if (result != null && !result.trim().equals("")) {
					fPath.setText(result);
				}
			}
		});
		
		return frame;
	}
	
	

}
