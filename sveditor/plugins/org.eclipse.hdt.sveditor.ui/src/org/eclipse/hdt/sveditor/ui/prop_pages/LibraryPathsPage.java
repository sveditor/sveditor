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


package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.hdt.sveditor.core.db.project.SVDBPath;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
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

public class LibraryPathsPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ILabelProvider {
	private ListViewer						fLibraryPathViewer;
	private SVProjectFileWrapper			fProjectWrapper;
	private List<SVDBPath>					fLibraryPaths;
	private Button							fAdd;
	private Button							fRemove;
	private Button							fEdit;
	private IProject						fProject;
	
	public LibraryPathsPage(IProject p) {
		fLibraryPaths = new ArrayList<SVDBPath>();
		fProject = p;
	}
	
	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
		
		fLibraryPaths.clear();
		for (SVDBPath p : fProjectWrapper.getLibraryPaths()) {
			fLibraryPaths.add(p.duplicate());
		}
	}


	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);

		frame.setLayout(new GridLayout(2, false));
		
		fLibraryPathViewer = new ListViewer(frame, SWT.BORDER);
		fLibraryPathViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fLibraryPathViewer.setContentProvider(this);
		fLibraryPathViewer.setLabelProvider(this);
		fLibraryPathViewer.setInput(fLibraryPaths);
		fLibraryPathViewer.addSelectionChangedListener(new ISelectionChangedListener() {
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
		return SVUiPlugin.getImage("/icons/eview16/sv_lib.gif");
	}

	public String getName() {
		return "Library Paths";
	}


	public void perfomOk() {
		fProjectWrapper.getLibraryPaths().clear();
		
		for (SVDBPath p : fLibraryPaths) {
			fProjectWrapper.getLibraryPaths().add(p.duplicate());
		}
	}

	public Object[] getElements(Object inputElement) {
		return fLibraryPaths.toArray();
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
			fLibraryPaths.add(path);
			fLibraryPathViewer.refresh();
		}
	}
	
	private void edit() {
		IStructuredSelection sel = (IStructuredSelection)fLibraryPathViewer.getSelection();
		SVDBPath elem = (SVDBPath)sel.getFirstElement();

		AddFilePathDialog dlg = new AddFilePathDialog(fAdd.getShell(), fProject, "Edit Path");
		dlg.setInitialPath(elem.getPath());
		
		if (dlg.open() == Window.OK) {
			elem.setPath(dlg.getPath());
			fLibraryPathViewer.refresh();
		}
	}
	
	private void remove() {
		IStructuredSelection sel = (IStructuredSelection)fLibraryPathViewer.getSelection();
		
		for (Object sel_o : sel.toList()) {
			fLibraryPaths.remove(sel_o);
		}
		
		fLibraryPathViewer.refresh();
	}

	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fLibraryPathViewer.getSelection();
		
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
