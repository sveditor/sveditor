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


import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
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

abstract public class AbstractNewSVItemFileWizardPage extends WizardPage {
	public static final String	SOURCE_FOLDER 	= "SOURCE_FOLDER";
	public static final String	NAME 			= "NAME";
	public static final String	FILE_NAME		= "FILE_NAME";
	
	protected AbstractNewSVItemFileWizard	fParent;
	
	protected Map<String, String>	fOptions;
	
	protected String				fFileExt;
	
	private Text					fSourceFolder;
	private Text					fName;
	private Text					fFileName;
	private Button					fFileNameDefault;
	
	protected Composite				fRootComposite;
	
	public AbstractNewSVItemFileWizardPage(
			AbstractNewSVItemFileWizard		parent,
			String 							title, 
			String 							type, 
			String 							description) {
		super(title, type, null);
		setDescription(description);
		
		fParent = parent;
		
		fFileExt = ".svh";
		fOptions = new HashMap<String, String>();
		
		setOption(NAME, "");
	}
	
	public String getOption(String key, String dflt) {
		if (fOptions.containsKey(key)) {
			return fOptions.get(key);
		} else {
			return dflt;
		}
	}
	
	public void setOption(String key, String val) {
		if (fOptions.containsKey(key)) {
			fOptions.remove(key);
		}
		fOptions.put(key, val);
	}
	
	abstract protected void createCustomContent(Composite c);
	
	protected void sourceFolderChanged() {
	}

	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		Label l;
		
		fRootComposite = new Composite(parent, SWT.NONE);
		fRootComposite.setLayout(new GridLayout());

		Composite src_c = new Composite(fRootComposite, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		l = new Label(src_c, SWT.NONE);
		l.setText("&Source Folder:");
		
		fSourceFolder = new Text(src_c, SWT.BORDER);
		fSourceFolder.setText(getOption(SOURCE_FOLDER, ""));
		fSourceFolder.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, false));
		fSourceFolder.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setOption(SOURCE_FOLDER, fSourceFolder.getText());
				sourceFolderChanged();
				validate();
			}
		});
		final Button sf_browse = new Button(src_c, SWT.PUSH);
		sf_browse.setText("&Browse");
		sf_browse.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(
						sf_browse.getShell());
				if (dlg.open() == Window.OK) {
					fSourceFolder.setText(dlg.getPath());
				}
				validate();
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		Composite s = new Composite(src_c, SWT.BORDER);
		GridData gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 3;
		gd.heightHint = 1;
		s.setLayoutData(gd);

		l = new Label(src_c, SWT.NONE);
		l.setText("&Name:");
		
		fName = new Text(src_c, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fName.setLayoutData(gd);
		fName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setOption(NAME, fName.getText());
				updateFilename();
				validate();
			}
		});

		l = new Label(src_c, SWT.NONE);
		l.setText("&Filename:");
		
		fFileName = new Text(src_c, SWT.BORDER);
		fFileName.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fFileName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setOption(FILE_NAME, fFileName.getText());
				validate();
			}
		});
		
		fFileNameDefault = new Button(src_c, SWT.CHECK);
		fFileNameDefault.setText("&Default Filename");
		fFileNameDefault.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				if (!fFileNameDefault.getSelection()) {
					fFileName.setEditable(true);
					fFileName.setEnabled(true);
				} else {
					fFileName.setEnabled(true);
					if (!getOption(NAME, "").equals("")) {
						fFileName.setText(getOption(NAME, "") + fFileExt);
					} else {
						fFileName.setText("");
					}
					fFileName.setEnabled(false);
					fFileName.setEditable(false);
				}
				validate();
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		fFileNameDefault.setSelection(true);
		fFileName.setEnabled(false);
		fFileName.setEditable(false);
	
		createCustomContent(src_c);
		
		// Set focus on name field
		fName.setFocus();
		
		setPageComplete(false);
		setControl(fRootComposite);
	}
	
	protected void updateFilename() {
		if (fFileNameDefault.getSelection()) {
			fFileName.setEnabled(true);
			if (!getOption(NAME, "").equals("")) {
				fFileName.setText(getOption(NAME, "") + fFileExt);
			} else {
				fFileName.setText("");
			}
			fFileName.setEnabled(false);
		}
	}
	
	protected void validate() {
		setErrorMessage(null);
		if (!SVCharacter.isSVIdentifier(getOption(NAME, ""))) {
			setErrorMessage("Invalid class name format");
		}
		
		IContainer c = SVFileUtils.getWorkspaceFolder(getOption(SOURCE_FOLDER, ""));
		if (c != null) {
			String filename_str = getOption(FILE_NAME, null);
			if (filename_str != null && !filename_str.equals("")) {
				IFile f = c.getFile(new Path(filename_str));
				if (f.exists()) {
					setErrorMessage("File \"" + filename_str + "\" exists");
				}
			}
		} else {
			setErrorMessage("Directory \"" + 
					getOption(SOURCE_FOLDER, "") + "\" does not exist");
		}
		
		setPageComplete((getErrorMessage() == null));
	}
	
	protected IProject findDestProject() {
		IContainer c = SVFileUtils.getWorkspaceFolder(getOption(SOURCE_FOLDER, ""));

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

}
