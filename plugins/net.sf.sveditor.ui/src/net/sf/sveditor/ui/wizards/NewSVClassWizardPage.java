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
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
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
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class NewSVClassWizardPage extends WizardPage {
	private Text					fSourceFolder;
	private String					fSourceFolderStr;
	
	private Text					fName;
	private String					fNameStr;
	
	private Text					fSuperClass;
//	private String					fSuperClassStr;
	private Button					fSuperClassBrowse;
	
	
	public NewSVClassWizardPage() {
		super("New SystemVerilog Class");
	}
	
	public void setSourceFolder(String folder) {
		fSourceFolderStr = folder;
	}
	
	public String getSourceFolder() {
		return fSourceFolderStr;
	}
	
	public String getName() {
		return fNameStr;
	}

	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		final Composite c = new Composite(parent, SWT.NONE);
		Label l;
		Button b;
		c.setLayout(new GridLayout());

		Composite src_c = new Composite(c, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		l = new Label(src_c, SWT.NONE);
		l.setText("Source Folder:");
		
		fSourceFolder = new Text(src_c, SWT.BORDER);
		if (fSourceFolderStr != null) {
			fSourceFolder.setText(fSourceFolderStr);
		}
		fSourceFolder.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, false));
		fSourceFolder.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fSourceFolderStr = fSourceFolder.getText();
				updateClassBrowseState();				
			}
		});
		
		fSuperClassBrowse = new Button(src_c, SWT.NONE);
		fSuperClassBrowse.setText("Browse");
		fSuperClassBrowse.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent e) {
				WorkspaceDirectoryDialog dlg = 
					new WorkspaceDirectoryDialog(c.getShell());
				if (dlg.open() == Window.OK) {
					fSourceFolder.setText(dlg.getPath());
				}
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		// TODO: Add divider
		Composite name_c = new Composite(c, SWT.NONE);
		name_c.setLayout(new GridLayout(2, false));
		name_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		l = new Label(name_c, SWT.NONE);
		l.setText("Name:");
		
		fName = new Text(name_c, SWT.BORDER);
		fName.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fNameStr = fName.getText();
			}
		});
		
		l = new Label(name_c, SWT.NONE);
		l.setText("Super Class:");
		
		Composite super_cls_c = new Composite(name_c, SWT.NONE);
		super_cls_c.setLayout(new GridLayout(2, false));
		super_cls_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSuperClass = new Text(super_cls_c, SWT.BORDER);
		fSuperClass.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		b = new Button(super_cls_c, SWT.NONE);
		b.setText("Browse");
		b.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				browseClass();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		

		setControl(c);
	}
	
	private void updateClassBrowseState() {
		fSuperClassBrowse.setEnabled((findDestProject() != null));
	}
	
	private IProject findDestProject() {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IResource r = null;
		IProject  p = null;

		try {
			if ((r = root.getFolder(new Path(fSourceFolderStr))) != null && r.exists()) {
				return r.getProject();
			}
		} catch (IllegalArgumentException e) {
			// ignore, since this probably means we're 
		}
		
		// See if this is a project root
		String pname = fSourceFolderStr;
		if (pname.startsWith("/")) {
			pname = pname.substring(1);
		}
		if (pname.endsWith("/")) {
			pname = pname.substring(0, pname.length()-1);
		}
		for (IProject p_t : root.getProjects()) {
			if (p_t.getName().equals(pname)) {
				p = p_t;
				break;
			}
		}
		
		return p;
	}
	
	private void browseClass() {
		IProject p = findDestProject();
		SVDBProjectData pdata = 
			SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
		
		BrowseClasses dlg = new BrowseClasses(
				fSuperClass.getShell(), pdata.getProjectIndexMgr());
		
		if (dlg.open() == Window.OK) {
			
		}
	}

}
