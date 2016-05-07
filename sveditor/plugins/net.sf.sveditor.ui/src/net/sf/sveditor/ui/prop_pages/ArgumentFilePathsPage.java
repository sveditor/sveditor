/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
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

public class ArgumentFilePathsPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ILabelProvider {
	private ListViewer						fArgFilePathViewer;
	private SVProjectFileWrapper			fProjectWrapper;
	private List<SVDBPath>					fArgFilePaths;
	private Button							fAdd;
	private Button							fRemove;
	private Button							fEdit;
	private IProject						fProject;
	
	public ArgumentFilePathsPage(IProject p) {
		fArgFilePaths = new ArrayList<SVDBPath>();
		fProject = p;
	}
	
	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
		
		fArgFilePaths.clear();
		for (SVDBPath p : fProjectWrapper.getArgFilePaths()) {
			fArgFilePaths.add(p.duplicate());
		}
	}


	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);

		frame.setLayout(new GridLayout(2, false));
		
		fArgFilePathViewer = new ListViewer(frame, SWT.BORDER);
		fArgFilePathViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fArgFilePathViewer.setContentProvider(this);
		fArgFilePathViewer.setLabelProvider(this);
		fArgFilePathViewer.setInput(fArgFilePaths);
		fArgFilePathViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelection();
			}
		});
		
		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, false, true));
		button_bar.setLayout(new GridLayout(1, true));
		
		fAdd = new Button(button_bar, SWT.PUSH);
		fAdd.setText("&Add");
		fAdd.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fAdd.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			public void widgetSelected(SelectionEvent e) {
				add();
			}
		});

		fEdit = new Button(button_bar, SWT.PUSH);
		fEdit.setText("&Edit");
		fEdit.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fEdit.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				edit();
			}
		});

		fRemove = new Button(button_bar, SWT.PUSH);
		fRemove.setText("&Remove");
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
		return SVUiPlugin.getImage("/icons/eview16/sv_lib.gif");
	}

	public String getName() {
		return "Argument Files";
	}


	public void perfomOk() {
		fProjectWrapper.getArgFilePaths().clear();
		
		for (SVDBPath p : fArgFilePaths) {
			fProjectWrapper.getArgFilePaths().add(p.duplicate());
		}
	}

	public Object[] getElements(Object inputElement) {
		return fArgFilePaths.toArray();
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
			fArgFilePaths.add(path);
			fArgFilePathViewer.refresh();
		}
	}
	
	private void edit() {
		IStructuredSelection sel = (IStructuredSelection)fArgFilePathViewer.getSelection();
		SVDBPath elem = (SVDBPath)sel.getFirstElement();

		AddFilePathDialog dlg = new AddFilePathDialog(fAdd.getShell(), fProject, "Edit Path");
		dlg.setInitialPath(elem.getPath());
		
		if (dlg.open() == Window.OK) {
			elem.setPath(dlg.getPath());
			fArgFilePathViewer.refresh();
		}
	}
	
	private void remove() {
		IStructuredSelection sel = (IStructuredSelection)fArgFilePathViewer.getSelection();
		
		for (Object sel_o : sel.toList()) {
			fArgFilePaths.remove(sel_o);
		}
		
		fArgFilePathViewer.refresh();
	}

	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fArgFilePathViewer.getSelection();
		
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
