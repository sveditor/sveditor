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


package org.eclipse.hdt.sveditor.ui.wizards;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByName;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindContentAssistNameMatcher;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindSuperClass;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.SelectionStatusDialog;

public class BrowseClasses extends SelectionStatusDialog 
	implements IStructuredContentProvider {
	
	private String					fSuperClass;
	
	private Text					fClassName;
	private String					fClassNameStr;
	private boolean					fModifyInProgress;
	
	private TableViewer				fClassList;
	private SVDBClassDecl			fSelectedClass;
	private ISVDBIndexIterator		fIndexIt;
	private List<SVDBItem>			fProposals;
	
	public BrowseClasses(Shell shell, ISVDBIndexIterator index_it) {
		super(shell);
		fIndexIt = index_it;
		fProposals = new ArrayList<SVDBItem>();
		setTitle("Browse Classes");
		setStatusLineAboveButtons(true);
	}
	
	public void setSuperClass(String superclass) {
		fSuperClass = superclass;
	}
	
	public void setClassName(String classname) {
		fClassNameStr = classname;
		if (fClassName != null) {
			fClassName.setText(fClassNameStr);
		}
	}
	
	public SVDBClassDecl getSelectedClass() {
		return fSelectedClass;
	}
	
	@Override
	protected Control createDialogArea(Composite parent) {
		Label l;
		GridData gd;
		
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout(2, false));
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.widthHint = 320;
		gd.heightHint = 320;
		c.setLayoutData(gd);
		
		l = new Label(c, SWT.NONE);
		l.setText("Name:");
		
		fClassName = new Text(c, SWT.BORDER);
		fClassName.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fClassName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fClassNameStr = fClassName.getText();
				if (!fModifyInProgress) {
					updateProposals();
				}
			}
		});
		
		fClassList = new TableViewer(c, SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		fClassList.getControl().setLayoutData(gd);
		fClassList.setContentProvider(this);
		fClassList.setLabelProvider(new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()));
		fClassList.setInput(fProposals);
		fClassList.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fClassList.getSelection();
				
				if (sel.getFirstElement() == null) {
					fSelectedClass = null;
					updateStatus(new Status(IStatus.ERROR, SVUiPlugin.PLUGIN_ID, "No class selected"));
				} else {
					fSelectedClass = (SVDBClassDecl)sel.getFirstElement();
					updateStatus(new Status(IStatus.OK, SVUiPlugin.PLUGIN_ID, 
							"Selected class \"" + fSelectedClass.getName() + "\""));
				}
			}
		});
		fClassList.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				okPressed();
			}
		});

		if (fClassNameStr != null) {
			fClassName.setText(fClassNameStr);
		} else {
			fClassName.setText("");
		}
		updateProposals();

		return c;
	}
	
	private void updateProposals() {
		SVDBFindByName finder = new SVDBFindByName(fIndexIt, 
				new SVDBFindContentAssistNameMatcher() {
					@Override
					public boolean match(ISVDBNamedItem it, String name) {
						return (!it.getName().startsWith("__sv_builtin") &&
								super.match(it, name));
					}
			});
		List<ISVDBItemBase> proposals = null;
		
		fProposals.clear();
		IStructuredSelection sel = (IStructuredSelection)fClassList.getSelection();
		if (fClassNameStr == null) {
			fClassNameStr = "";
		}
		proposals = finder.findItems(fClassNameStr, SVDBItemType.ClassDecl);
		for (ISVDBItemBase p : proposals) {
			fProposals.add((SVDBItem)p);
		}
		
		if (fSuperClass != null) {
			filter_by_superclass();
		}

		for (SVDBItem cls : fProposals) {
			if (cls.getName().equals(fClassNameStr)) {
				sel = new StructuredSelection(cls);
			}
		}
		fClassList.setSelection(sel);
		fClassList.refresh();
		
		sel = (IStructuredSelection)fClassList.getSelection();
		if (sel != null && sel.getFirstElement() != null) {
			fSelectedClass = (SVDBClassDecl)sel.getFirstElement();
			updateStatus(new Status(IStatus.OK, SVUiPlugin.PLUGIN_ID, 
					"Selected class \"" + fSelectedClass.getName() + "\""));
		} else {
			updateStatus(new Status(IStatus.ERROR, SVUiPlugin.PLUGIN_ID, "No class selected"));
		}
	}
	
	private void filter_by_superclass() {
		SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIt);
		
		for (int i=0; i<fProposals.size(); i++) {
			SVDBClassDecl cls = (SVDBClassDecl)fProposals.get(i);
			boolean found = false;
			
			// Search each class' super-class hierarchy looking for
			// the desired super-class
			while (cls != null) {
				SVDBClassDecl super_cls = finder.find(cls);
				if (super_cls != null && super_cls.getName().equals(fSuperClass)) {
					found = true;
					break;
				}
				cls = super_cls;
			}
			
			if (!found) {
				fProposals.remove(i);
				i--;
			}
		}
	}

	@Override
	protected void computeResult() {
	}

	// ContentProvider implementation
	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	public Object[] getElements(Object inputElement) {
		return fProposals.toArray();
	}
}
