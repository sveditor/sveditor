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
package net.sf.sveditor.ui.wizards.new_filelist;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.ui.WorkspaceDirectoryTreeViewer;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.events.VerifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewFileListWizardFirstPage extends WizardPage {
	private WorkspaceDirectoryTreeViewer		fTreeView;
	private IContainer							fInitialSel;
	private IContainer							fOutputDir;
	private Text								fFilenameText;
	private String								fFilename;
	private boolean								fAddToProject;
	private Button								fAddToProjectCheck;
	private	List<String> 						fArgFileExts;
	private StringBuilder						fArgFileExtsList;
	
	public NewFileListWizardFirstPage() {
		super("Filelist Name and Location", 
				"Specify filename and destination folder", null);
		fArgFileExts = SVCorePlugin.getDefault().getDefaultArgFileExts();
		fArgFileExtsList = new StringBuilder();
		for (String ext : fArgFileExts) {
			fArgFileExtsList.append(ext + ", ");
		}
		fArgFileExtsList.setLength(fArgFileExtsList.length()-2);
	}
	
	public String getFilename() {
		return fFilename;
	}
	
	public IContainer getOutputDir() {
		return fOutputDir;
	}
	
	public boolean getAddToProject() {
		return fAddToProject;
	}
	
	public void init(IStructuredSelection sel) {
		fInitialSel = null;
		if (sel != null && !sel.isEmpty()) {
			Object r_obj = sel.getFirstElement();
			IResource r = null;
			
			if (r_obj instanceof IResource) {
				r = (IResource)r_obj;
			} else if (r_obj instanceof IAdaptable) {
				r = (IResource)((IAdaptable)r_obj).getAdapter(IResource.class);
			}
		
			if (r != null) {
				if (r instanceof IContainer) {
					fInitialSel = (IContainer)r;
				} else if (r instanceof IFile) {
					fInitialSel = ((IFile)r).getParent();
				}
			}
		}
		
		if (fInitialSel != null && fTreeView != null) {
			fTreeView.setSelection(new StructuredSelection(fInitialSel));
		}
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd;
		Composite c = new Composite(parent, SWT.NONE+SWT.SINGLE);
		c.setLayout(new GridLayout(2, false));

		fTreeView = new WorkspaceDirectoryTreeViewer(c, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		fTreeView.getTree().setLayoutData(gd);
		
		fTreeView.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeView.getSelection();
				
				if (sel == null || sel.isEmpty()) {
					fOutputDir = null;
				} else {
					fOutputDir = (IContainer)sel.getFirstElement();
				}
				
				validate();
			}
		});
		
		Label l = new Label(c, SWT.NONE);
		l.setText("&Filename: ");
		
		fFilenameText = new Text(c, SWT.BORDER);
		fFilenameText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fFilenameText.addVerifyListener(new VerifyListener() {
			
			@Override
			public void verifyText(VerifyEvent e) {
				if (e.character == '/' || e.character == '\\') {
					e.doit = false;
				}
			}
		});
		fFilenameText.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				fFilename = fFilenameText.getText().trim();
			
				validate();
			}
		});
	
		l = new Label(c, SWT.NONE);
		l.setText("&Add to Project Settings: ");
		fAddToProjectCheck = new Button(c, SWT.CHECK);
		fAddToProject = true;
		fAddToProjectCheck.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				fAddToProject = fAddToProjectCheck.getSelection();
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) { }
		});
		
		if (fInitialSel != null) {
			fTreeView.setSelection(new StructuredSelection(fInitialSel));
		}
		fAddToProjectCheck.setSelection(true);

		setControl(c);
	}
	
	private void validate() {
		String msg = null, warn_msg = null;
		
		if (msg == null && fOutputDir == null) {
			msg = "Select the destination directory";
		}
		
		if (msg == null) {
			// Validate filename
			if (fFilename == null || fFilename.equals("")) {
				msg = "Specify the file name";
			} else {
				try {
					IFile file = fOutputDir.getFile(new Path(fFilename));
					if (file.exists()) {
						msg = "File exists";
					}
				} catch (Exception e) {
					msg = "Invalid filename: " + e.getMessage();
				}
			}
		}
		
		if (msg == null && warn_msg == null) {
			// Check whether the name is reasonable
			String ext = SVFileUtils.getPathExt(fFilename);
			
			if (ext == null) {
				ext = "";
			}
			
			if (!fArgFileExts.contains(ext)) {
				warn_msg = "File extension \"" + ext + "\" is discouraged. Use: " + 
						fArgFileExtsList;
			}
		}
	
		setErrorMessage(msg);
		setPageComplete(msg == null);

		setMessage(warn_msg, DialogPage.WARNING);
	}

}
