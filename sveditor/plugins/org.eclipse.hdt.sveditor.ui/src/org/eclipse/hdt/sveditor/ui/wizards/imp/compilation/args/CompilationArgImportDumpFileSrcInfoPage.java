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
package org.eclipse.hdt.sveditor.ui.wizards.imp.compilation.args;


import java.io.InputStream;

import org.eclipse.hdt.sveditor.ui.WorkspaceDirectoryDialog;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class CompilationArgImportDumpFileSrcInfoPage extends WizardPage {
	private Text						fDestDirText;
	private String						fDestDir;
	private Button						fDestDirBrowse;
	
	private Text						fDestFileText;
	private String						fDestFile;
	
	private Button						fAddToProjectButton;
	private boolean						fAddToProject;
	
	private Text						fSrcFile;
	private Button						fSrcFileBrowse;
	private String						fSrcFileStr;
	
	private Text						fImportCmdArgsText;
	
	private String						fCapturedArgs;
	
	private SVDBWSFileSystemProvider	fFSProvider;
	
	public CompilationArgImportDumpFileSrcInfoPage() {
		super("Source Info");
		fFSProvider = new SVDBWSFileSystemProvider();
		
		fSrcFileStr = "";
		fDestDir = "";
	}
	
	public void setDestDir(String dir) {
		fDestDir = (dir != null)?dir:"";
		if (fDestDirText != null) {
			fDestDirText.setText(fDestDir);
		}
	}
	
	public void setSrcDir(String dir) {
		fSrcFileStr = (dir != null)?dir:"";
		if (fSrcFile != null) {
			fSrcFile.setText(fSrcFileStr);
		}
	}
	
	public String getDestFile() {
		return fDestFile;
	}
	
	public String getDestDir() {
		return fDestDir;
	}
	
	public String getCapturedArgs() {
		return fCapturedArgs;
	}
	
	public boolean getAddToProject() {
		return fAddToProject;
	}

	public void createControl(Composite parent) {
		GridData gd;
		SashForm sash = new SashForm(parent,  SWT.VERTICAL);
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Composite top = new Composite(sash, SWT.BORDER);
		top.setLayout(new GridLayout(3, false));

		Label l;
		Group g;
	
		// Output information
		l = new Label(top, SWT.NONE);
		l.setText("Destination Directory:");
		fDestDirText = new Text(top, SWT.BORDER);
		fDestDirText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fDestDirBrowse = new Button(top, SWT.PUSH);
		fDestDirBrowse.setText("Browse...");
		fDestDirBrowse.addSelectionListener(selectionListener);
		
		l = new Label(top, SWT.NONE);
		l.setText("Destination File:");
		fDestFileText = new Text(top, SWT.BORDER);
		fDestFileText.addModifyListener(textModifyListener);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fDestFileText.setLayoutData(gd);
		
		l = new Label(top, SWT.NONE);
		l.setText("Update Project Settings:");
		fAddToProjectButton = new Button(top, SWT.CHECK);
		fAddToProjectButton.addSelectionListener(selectionListener);
		gd = new GridData(SWT.RIGHT, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fAddToProjectButton.setLayoutData(gd);
		fAddToProjectButton.setSelection(true);
		fAddToProject = true;

		// Source file
		l = new Label(top, SWT.NONE);
		l.setText("Source File:");
		
		fSrcFile = new Text(top, SWT.SINGLE+SWT.BORDER);
		fSrcFile.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSrcFile.addModifyListener(textModifyListener);
		
		fSrcFileBrowse = new Button(top, SWT.PUSH);
		fSrcFileBrowse.setText("Browse");
		fSrcFileBrowse.addSelectionListener(selectionListener);
	
		Composite bottom = new Composite(sash, SWT.BORDER);
		bottom.setLayout(new GridLayout());
		bottom.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		g = new Group(bottom, SWT.SHADOW_ETCHED_IN);
		g.setText("Compilation Argument Dumpfile");
		g.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		g.setLayoutData(gd);
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fImportCmdArgsText = new Text(g,
				SWT.MULTI+SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		fImportCmdArgsText.addModifyListener(textModifyListener);
		fImportCmdArgsText.setLayoutData(gd);
		
		fDestDirText.setText(fDestDir);
		fSrcFile.setText(fSrcFileStr);
		
		validate();
		
		setControl(sash);
	}
	
	private void validate() {
		setErrorMessage(null);
		
		if (fDestDirText.getText().trim().equals("") ||
				!fFSProvider.isDir("${workspace_loc}" + fDestDirText.getText().trim())) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a destination directory");
			}
		}
		
		if (fDestFileText.getText().trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify a destination file");
			}
		}

		// Check whether src path exists
		if (fSrcFile.getText().trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Must specify source file");
			}
		}
		
		if (!fFSProvider.fileExists(fSrcFile.getText().trim())) {
			if (getErrorMessage() == null) {
				setErrorMessage("Source file does not exist");
			}
		} else if (fCapturedArgs == null || fCapturedArgs.trim().equals("")) {
			if (getErrorMessage() == null) {
				setErrorMessage("Dump file is empty");
			}
		}
		
		setPageComplete((getErrorMessage() == null));
	}

	private ModifyListener				textModifyListener = new ModifyListener() {
		public void modifyText(ModifyEvent e) {
			Object src = e.getSource();
			
			if (src == fDestDirText) {
				fDestDir = fDestDirText.getText();
			}
			
			if (src == fDestFileText) {
				fDestFile = fDestFileText.getText();
			}
			
			if (src == fImportCmdArgsText) {
				fCapturedArgs = fImportCmdArgsText.getText();
			}
			
			if (src == fSrcFile) {
				fSrcFileStr = fSrcFile.getText();
				if (fFSProvider.fileExists(fSrcFile.getText().trim())) {
					final StringBuilder sb = new StringBuilder();
					Job j = new Job("Read Dumpfile") {
						
						@Override
						protected IStatus run(IProgressMonitor monitor) {
							// Read in the file
							InputStream in = fFSProvider.openStream(fSrcFileStr);
							String file = SVFileUtils.readInput(in);
							sb.append(file);
							fFSProvider.closeStream(in);
							// TODO Auto-generated method stub
							return Status.OK_STATUS;
						}
					};
					j.schedule();
					try {
						j.join();
					} catch (InterruptedException ex) {}
					
					fImportCmdArgsText.setText(sb.toString());
				}
			}

			validate();
		}
	};
	
	private SelectionListener				selectionListener = new SelectionListener() {
		
		public void widgetSelected(SelectionEvent e) {
			Object src = e.getSource();
			
			if (src == fDestDirBrowse) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(fDestDirBrowse.getShell());
				dlg.setInitialPath(fDestDirText.getText().trim());
				
				if (dlg.open() == Window.OK) {
					fDestDirText.setText(dlg.getPath());
				}
			} else if (src == fSrcFileBrowse) {
				BrowseFilePathDialog dlg = new BrowseFilePathDialog(fSrcFile.getShell());
				dlg.setInitialPath(fSrcFile.getText());
				
				if (dlg.open() == Window.OK) {
					fSrcFile.setText(dlg.getPath());
				}
			} else if (src == fAddToProjectButton) {
				fAddToProject = fAddToProjectButton.getSelection();
			}
		}
		
		public void widgetDefaultSelected(SelectionEvent e) { }
	};

}
