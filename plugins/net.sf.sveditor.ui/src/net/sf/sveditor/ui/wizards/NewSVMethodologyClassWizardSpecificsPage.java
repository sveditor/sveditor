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


package net.sf.sveditor.ui.wizards;


import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.methodology_templates.MethodologyTemplate;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
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

public class NewSVMethodologyClassWizardSpecificsPage extends WizardPage {
	private String					fSourceFolderStr;
	// private MethodologyTemplate		fTemplate;
	
	// private String					fNameStr;

	private Text					fSuperClass;
	private String					fSuperClassStr;
	private Button					fSuperClassBrowse;
	
	public NewSVMethodologyClassWizardSpecificsPage() {
		super("New SystemVerilog Class", "SystemVerilog Class", null);
		setDescription("Create a new SystemVerilog class");
	}
	
	public void setSourceFolder(String folder) {
		fSourceFolderStr = folder;
	}
	
	public void setTemplate(MethodologyTemplate template) {
		// fTemplate = template;
	}
	
	public String getSuperClass() {
		return fSuperClassStr;
	}
	
	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		Label l;
		
		// fNameStr = "";
		
		final Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());

		Composite src_c = new Composite(c, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		
		Composite s = new Composite(src_c, SWT.BORDER);
		GridData gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 3;
		gd.heightHint = 1;
		s.setLayoutData(gd);

		/** CHANGE **/
		l = new Label(src_c, SWT.NONE);
		l.setText("Super Class:");
		
		fSuperClass = new Text(src_c, SWT.BORDER);
		fSuperClass.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSuperClass.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fSuperClassStr = fSuperClass.getText();
				validate();
			}
		});
		fSuperClassBrowse = new Button(src_c, SWT.NONE);
		fSuperClassBrowse.setText("Browse");
		fSuperClassBrowse.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				browseClass();
				validate();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		Group group = new Group(src_c, SWT.BORDER);
		group.setText("Style Options");
		group.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		group.setLayoutData(gd);
		
		setPageComplete(false);
		setControl(c);
	}
	
	private void validate() {
		setErrorMessage(null);
		/*
		if (!SVCharacter.isSVIdentifier(fNameStr)) {
			setErrorMessage("Invalid class name format");
		}
		
		IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);
		if (c != null) {
			if (fFileNameStr != null && !fFileNameStr.equals("")) {
				IFile f = c.getFile(new Path(fFileNameStr));
				if (f.exists()) {
					setErrorMessage("File \"" + fFileNameStr + "\" exists");
				}
			}
		} else {
			setErrorMessage("Directory \"" + 
					fSourceFolderStr + "\" does not exist");
		}
		
		setPageComplete((getErrorMessage() == null));
		 */
	}
	
	/*
	private void updateClassBrowseState() {
		fSuperClassBrowse.setEnabled((findDestProject() != null));
	}
	 */
	
	private IProject findDestProject() {
		IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);

		if (c == null) {
			return null;
		} else if (c instanceof IProject) {
			return (IProject)c;
		} else {
			return c.getProject();
		}
	}
	
	public SVDBProjectData getProjectData() {
		IProject p = findDestProject();
		if (p == null) {
			return null;
		}

		SVDBProjectData pdata = 
			SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
		
		return pdata;
	}
	
	private void browseClass() {
		SVDBProjectData pdata = getProjectData();
		
		BrowseClasses dlg = new BrowseClasses(
				fSuperClass.getShell(), pdata.getProjectIndexMgr());
		dlg.setClassName(fSuperClassStr);
		
		if (dlg.open() == Window.OK) {
			SVDBModIfcDecl cls = dlg.getSelectedClass();
			if (cls != null) {
				fSuperClass.setText(cls.getName());
			}
		}
	}

}
