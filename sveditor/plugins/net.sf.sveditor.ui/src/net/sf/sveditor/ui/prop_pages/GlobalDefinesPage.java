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

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
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

public class GlobalDefinesPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ITableLabelProvider {
	private TableViewer						fGlobalDefines;
	private SVProjectFileWrapper			fProjectWrapper;
	private List<Tuple<String, String>>		fDefineList;
	private Button							fAdd;
	private Button							fRemove;
	private Button							fEdit;
//	private IProject						fProject;
	
	public GlobalDefinesPage(IProject p) {
		fDefineList = new ArrayList<Tuple<String, String>>();
//		fProject = p;
	}
	
	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
		
		fDefineList.clear();
		for (Tuple<String, String> p : fProjectWrapper.getGlobalDefines()) {
			Tuple<String, String> dup = 
				new Tuple<String, String>(p.first(), p.second());
			fDefineList.add(dup);
		}
	}


	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);

		frame.setLayout(new GridLayout(2, false));
		
		fGlobalDefines = new TableViewer(frame, SWT.MULTI + SWT.BORDER);
		fGlobalDefines.getTable().setHeaderVisible(true);
		fGlobalDefines.getTable().setLinesVisible(true);
		
		TableViewerColumn tc = new TableViewerColumn(fGlobalDefines, SWT.NONE);
		tc.getColumn().setText("Name");
		tc.getColumn().setWidth(100);

		tc = new TableViewerColumn(fGlobalDefines, SWT.NONE);
		tc.getColumn().setText("Value");
		tc.getColumn().setWidth(100);

		fGlobalDefines.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		
		fGlobalDefines.setContentProvider(this);
		fGlobalDefines.setLabelProvider(this);
		fGlobalDefines.setInput(fDefineList);
		fGlobalDefines.addSelectionChangedListener(new ISelectionChangedListener() {
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
		return SVUiPlugin.getImage("/icons/edecl16/define_obj.gif");
	}

	public String getName() {
		return "Global Defines";
	}


	public void perfomOk() {
		fProjectWrapper.getGlobalDefines().clear();
		
		for (Tuple<String, String> p : fDefineList) {
			Tuple<String, String> dup = 
				new Tuple<String, String>(p.first(), p.second());
			fProjectWrapper.getGlobalDefines().add(dup);
		}
	}

	public Object[] getElements(Object inputElement) {
		return fDefineList.toArray();
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	
	/*
	public String getText(Object element) {
		if (element instanceof SVDBPath) {
			return ((SVDBPath)element).getPath();
		}
		return null;
	}
	 */
	
	public Image getColumnImage(Object element, int columnIndex) {
		return null;
	}

	@SuppressWarnings("unchecked")
	public String getColumnText(Object element, int columnIndex) {
		Tuple<String, String> def = (Tuple<String, String>)element;
		
		return (columnIndex == 0)?def.first():def.second();
	}

	private void add() {
		AddDefineDialog dlg = new AddDefineDialog(fAdd.getShell());
		
		if (dlg.open() == Window.OK) {
			Tuple<String, String> path = new Tuple<String, String>(
					dlg.getName(), dlg.getValue());
			fDefineList.add(path);
			fGlobalDefines.refresh();
		}
	}
	
	@SuppressWarnings("unchecked")
	private void edit() {
		IStructuredSelection sel = (IStructuredSelection)fGlobalDefines.getSelection();
		Tuple<String, String> elem = (Tuple<String, String>)sel.getFirstElement();

		AddDefineDialog dlg = new AddDefineDialog(fAdd.getShell());
		dlg.setInitialName(elem.first());
		dlg.setInitialValue(elem.second());
		
		if (dlg.open() == Window.OK) {
			elem.setFirst(dlg.getName());
			elem.setSecond(dlg.getValue());
			fGlobalDefines.refresh();
		}
	}
	
	private void remove() {
		IStructuredSelection sel = (IStructuredSelection)fGlobalDefines.getSelection();
		
		for (Object sel_o : sel.toList()) {
			fDefineList.remove(sel_o);
		}
		
		fGlobalDefines.refresh();
	}

	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fGlobalDefines.getSelection();
		
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
