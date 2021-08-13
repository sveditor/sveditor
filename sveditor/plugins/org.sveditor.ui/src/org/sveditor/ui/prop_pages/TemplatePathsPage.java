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

import java.util.ArrayList;
import java.util.List;

import org.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.sveditor.core.db.project.SVDBPath;
import org.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

public class TemplatePathsPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ILabelProvider {
	private ListViewer						fTemplatePathViewer;
	private SVProjectFileWrapper			fProjectWrapper;
	private List<SVDBPath>					fTemplatePaths;
	private Button							fAdd;
	private Button							fRemove;
	private Button							fEdit;
	private IProject						fProject;
	
	public TemplatePathsPage(IProject p) {
		fTemplatePaths = new ArrayList<SVDBPath>();
		fProject = p;
	}
	
	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
		
		fTemplatePaths.clear();
		for (SVDBPath p : fProjectWrapper.getTemplatePaths()) {
			fTemplatePaths.add(p.duplicate());
		}
	}


	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);

		frame.setLayout(new GridLayout(2, false));
		
		fTemplatePathViewer = new ListViewer(frame, SWT.BORDER);
		fTemplatePathViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fTemplatePathViewer.setContentProvider(this);
		fTemplatePathViewer.setLabelProvider(this);
		fTemplatePathViewer.setInput(fTemplatePaths);
		fTemplatePathViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelection();
			}
		});
		
		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, false, true));
		button_bar.setLayout(new GridLayout(1, true));
		
		fAdd = new Button(button_bar, SWT.PUSH);
		fAdd.setText("Add");
		fAdd.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fAdd.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			public void widgetSelected(SelectionEvent e) {
				add();
			}
		});

		fEdit = new Button(button_bar, SWT.PUSH);
		fEdit.setText("Edit");
		fEdit.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fEdit.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				edit();
			}
		});

		fRemove = new Button(button_bar, SWT.PUSH);
		fRemove.setText("Remove");
		fRemove.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fRemove.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				remove();
			}
		});


		updateSelection();
		
		return frame;
	}

	public Image getIcon() {
//FIXME: missed image for Eclipse HDT
		return SVUiPlugin.getImage(
				"org.sveditor.svt.ui", "/icons/eview16/generate_template_class.gif");
	}

	public String getName() {
		return "Template Paths";
	}


	public void perfomOk() {
		fProjectWrapper.getTemplatePaths().clear();
		
		for (SVDBPath p : fTemplatePaths) {
			fProjectWrapper.addTemplatePath(p.duplicate());
		}
	}

	public Object[] getElements(Object inputElement) {
		return fTemplatePaths.toArray();
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}


	public Image getImage(Object element) {
		return null;
	}

	public String getText(Object element) {
		if (element instanceof SVDBPath) {
			return ((SVDBPath)element).getPath();
		}
		return null;
	}
	
	private void add() {
		AddFilePathDialog dlg = new AddFilePathDialog(fAdd.getShell(), fProject, "Add File");
		
		if (dlg.open() == Window.OK) {
			SVDBPath path = new SVDBPath(dlg.getPath(), false);
			fTemplatePaths.add(path);
			fTemplatePathViewer.refresh();
		}
	}
	
	private void edit() {
		IStructuredSelection sel = (IStructuredSelection)fTemplatePathViewer.getSelection();
		SVDBPath elem = (SVDBPath)sel.getFirstElement();

		AddFilePathDialog dlg = new AddFilePathDialog(fAdd.getShell(), fProject, "Edit Path");
		dlg.setInitialPath(elem.getPath());
		
		if (dlg.open() == Window.OK) {
			elem.setPath(dlg.getPath());
			fTemplatePathViewer.refresh();
		}
	}
	
	private void remove() {
		IStructuredSelection sel = (IStructuredSelection)fTemplatePathViewer.getSelection();
		
		for (Object sel_o : sel.toList()) {
			fTemplatePaths.remove(sel_o);
		}
		
		fTemplatePathViewer.refresh();
	}

	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fTemplatePathViewer.getSelection();
		
		fAdd.setEnabled(true);
		if (sel.getFirstElement() == null) {
			fRemove.setEnabled(false);
			fEdit.setEnabled(false);
		} else {
			if (sel.size() == 1) {
				fEdit.setEnabled(true);
			} else {
				fEdit.setEnabled(false);
			}
			fRemove.setEnabled(true);
		}
	}

	
	public void dispose() {}
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
	public void addListener(ILabelProviderListener listener) {}
	public void removeListener(ILabelProviderListener listener) {}
	
}
