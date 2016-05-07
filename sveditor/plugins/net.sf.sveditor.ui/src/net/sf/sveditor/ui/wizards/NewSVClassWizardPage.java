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
import net.sf.sveditor.core.db.project.SVDBProjectData;

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
	
	public static final String		SUPER_CLASS  = "SUPER_CLASS";
	public static final String		OVERRIDE_NEW = "OVERRIDE_NEW";
	
	private Text					fSuperClass;
	private Button					fSuperClassBrowse;
	
	private Button					fOverrideNew;
	
	public NewSVClassWizardPage() {
		super("New SystemVerilog Class", "SystemVerilog Class", 
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
		
		Group group = new Group(src_c, SWT.BORDER);
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
}
