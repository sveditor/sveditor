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


package org.eclipse.hdt.sveditor.ui;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class WorkspaceFileDialog extends Dialog {
	private String 				fPathStr;
	private TreeViewer			fTreeViewer;
	private boolean				fSelectFiles = true;
	private String				fTitle;
	
	
	public WorkspaceFileDialog(Shell shell, String title) {
		super(shell);
		fTitle = title;
	}
	public WorkspaceFileDialog(Shell shell) {
		super(shell);
		fTitle = "Select File";
	}

	public String getPath() {
		return fPathStr;
	}
	
	public void setSelectFiles(boolean sel_files) {
		fSelectFiles = sel_files;
	}
	
	public void configureShell (Shell shell) {
		super.configureShell(shell);
		shell.setText(fTitle);
	}

	@Override
	protected Control createDialogArea(Composite p) {
		Composite parent = new Composite(p, SWT.NONE);
		parent.setLayout(new GridLayout(1, true));
		
		fTreeViewer = new TreeViewer(parent);
		
		GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.widthHint = 300;
		gd.heightHint = 300;
		fTreeViewer.getControl().setLayoutData(gd);
		
		fTreeViewer.setContentProvider(new WorkbenchContentProvider());
		fTreeViewer.setLabelProvider(new WorkbenchLabelProvider());
		fTreeViewer.setInput(ResourcesPlugin.getWorkspace());
		
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
				if (fSelectFiles) {
					if (sel.getFirstElement() != null && 
							sel.getFirstElement() instanceof IFile) {
						fPathStr = ((IFile)sel.getFirstElement()).getFullPath().toOSString();
						getButton(IDialogConstants.OK_ID).setEnabled(true);
					} else {
						getButton(IDialogConstants.OK_ID).setEnabled(false);
					}
				} else {
					if (sel.getFirstElement() != null && 
							sel.getFirstElement() instanceof IContainer) {
						fPathStr = ((IContainer)sel.getFirstElement()).getFullPath().toOSString();
						getButton(IDialogConstants.OK_ID).setEnabled(true);
					} else {
						getButton(IDialogConstants.OK_ID).setEnabled(false);
					}
				}
			}
		});

		return fTreeViewer.getControl();
	}
}
