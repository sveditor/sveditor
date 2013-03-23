/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui;

import net.sf.sveditor.core.SVFileUtils;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class WorkspaceDirectoryDialog extends Dialog {
	private String 				fPathStr;
	private TreeViewer			fTreeViewer;
	
	
	public WorkspaceDirectoryDialog(Shell shell) {
		super(shell);
	}

	public String getPath() {
		return fPathStr;
	}
	
	public void setInitialPath(String path) {
		fPathStr = path;
		
		if (fTreeViewer != null) {
			IContainer c = SVFileUtils.getWorkspaceFolder(fPathStr);
			if (c != null) {
				fTreeViewer.setSelection(new StructuredSelection(c), true);
			}
		}
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
		fTreeViewer.addFilter(new ViewerFilter() {

			@Override
			public boolean select(Viewer viewer, Object parentElement,
					Object element) {
				return (element instanceof IContainer);
			}
		});
		fTreeViewer.setLabelProvider(new WorkbenchLabelProvider());
		fTreeViewer.setInput(ResourcesPlugin.getWorkspace());
		
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
				if (sel.getFirstElement() != null) {
					fPathStr = ((IContainer)sel.getFirstElement()).getFullPath().toOSString();
				}
			}
		});
	
		if (fPathStr != null) {
			IContainer c = SVFileUtils.getWorkspaceFolder(fPathStr);
			if (c != null) {
				fTreeViewer.setSelection(new StructuredSelection(c), true);
			}
		}

		return fTreeViewer.getControl();
	}
}
