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


package net.sf.sveditor.ui.wizards;


import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.search.SVDBAllTypeMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;
import net.sf.sveditor.ui.editor.outline.SVOutlineLabelProvider;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
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
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewSVClassWizardPage extends AbstractNewSVItemFileWizardPage {
	
	public static final String		SUPER_CLASS    = "SUPER_CLASS";
	public static final String		OVERRIDE_NEW   = "OVERRIDE_NEW";
	public static final String		ADD_TO_PACKAGE = "ADD_TO_PACKAGE";
	public static final String		PACKAGE        = "PACKAGE";
	
	private Text					fSuperClass;
	private Button					fSuperClassBrowse;
	
	private Button					fOverrideNew;
	private Button					fAddToPackage;
	private ListViewer				fPackageList;
	
	public NewSVClassWizardPage(AbstractNewSVItemFileWizard parent) {
		super(parent, "New SystemVerilog Class", 
				"SystemVerilog Class", 
				"Create a new SystemVerilog class");
		setOption(OVERRIDE_NEW, "true");
	}
	
	@Override
	protected void createCustomContent(Composite src_c) {
		Label l;
		GridData gd;
		
		l = new Label(src_c, SWT.NONE);
		l.setText("Super &Class:");
		
		fSuperClass = new Text(src_c, SWT.BORDER);
		fSuperClass.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSuperClass.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setOption(SUPER_CLASS, fSuperClass.getText());
				validate();
			}
		});
		fSuperClassBrowse = new Button(src_c, SWT.NONE);
		fSuperClassBrowse.setText("Bro&wse");
		fSuperClassBrowse.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				browseClass();
				validate();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		Group group = new Group(src_c, SWT.NONE);
		group.setText("Style &Options");
		group.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		group.setLayoutData(gd);
		
		fOverrideNew = new Button(group, SWT.CHECK);
		fOverrideNew.setText("I&mplement new()");
		fOverrideNew.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				setOption(OVERRIDE_NEW, (fOverrideNew.getSelection())?"true":"false");
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		fOverrideNew.setSelection(true);

		Group add_to_pkg = new Group(group, SWT.NONE);
		add_to_pkg.setText("Add to Package");
		add_to_pkg.setLayout(new GridLayout(2, false));
		add_to_pkg.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fAddToPackage = new Button(add_to_pkg, SWT.CHECK);
		fAddToPackage.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				setOption(ADD_TO_PACKAGE, (fAddToPackage.getSelection())?"true":"false");
				fPackageList.getControl().setEnabled(fAddToPackage.getSelection());
				// Ensure Next enablement tracks 
				fParent.getContainer().updateButtons();
			
				// Auto-set the selection
				if (fPackageList.getSelection().isEmpty()) {
					Object first = fPackageList.getElementAt(0);
					if (first != null) {
						fPackageList.setSelection(new StructuredSelection(first));
					}
				}
				validate();
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		fPackageList = new ListViewer(add_to_pkg, SWT.V_SCROLL+SWT.SINGLE);
		fPackageList.getList().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fPackageList.setContentProvider(new IStructuredContentProvider() {
			
			@Override
			public Object[] getElements(Object inputElement) {
				if (inputElement instanceof ISVDBIndexIterator) {
				ISVDBIndexIterator index_it = (ISVDBIndexIterator)inputElement;
				List<SVDBDeclCacheItem> pkg_list = index_it.findGlobalScopeDecl(
						new NullProgressMonitor(), null, 
						new SVDBFindByTypeMatcher(SVDBItemType.PackageDecl));
				return pkg_list.toArray();
				} else {
					return new Object[0];
				}
			}
		});
		fPackageList.setLabelProvider(new SVOutlineLabelProvider());
		fPackageList.setInput(fParent.getIndexIterator(new NullProgressMonitor()));
		fPackageList.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fPackageList.getSelection();
				
				Object pkg = sel.getFirstElement();
				
				if (pkg != null && pkg instanceof SVDBDeclCacheItem) {
					setOption(PACKAGE, ((SVDBDeclCacheItem)pkg).getName());
				}
			
				validate();
			}
		});
	
		// Initially disable add-to-package mode
		fAddToPackage.setSelection(false);
		fPackageList.getList().setEnabled(false);
		
	}

	@Override
	protected void sourceFolderChanged() {
		updateClassBrowseState();
	}

	private void updateClassBrowseState() {
		fSuperClassBrowse.setEnabled((findDestProject() != null));
	}
	
	private void browseClass() {
		SVDBProjectData pdata = getProjectData();
		
		BrowseClasses dlg = new BrowseClasses(
				fSuperClass.getShell(), pdata.getProjectIndexMgr());
		dlg.setClassName(getOption(SUPER_CLASS, ""));
		
		if (dlg.open() == Window.OK) {
			SVDBClassDecl cls = dlg.getSelectedClass();
			if (cls != null) {
				fSuperClass.setText(cls.getName());
			}
		}
	}

	@Override
	protected void validate() {
		super.validate();
		
		if (getErrorMessage() == null) {
			// Continue checking
			if (fAddToPackage.getSelection()) {
				// Get the current selection
				IStructuredSelection sel = (IStructuredSelection)fPackageList.getSelection();
				
				if (sel.isEmpty()) {
					setErrorMessage("Must select a package");
				}
			}
		}
	}
	
}
