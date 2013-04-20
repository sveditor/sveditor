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


package net.sf.sveditor.ui.wizards.templates;


import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.svt.core.templates.ITemplateParameterProvider;
import net.sf.sveditor.svt.core.templates.TemplateInfo;
import net.sf.sveditor.svt.core.templates.TemplateParameterProvider;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;

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

public class SVTemplateParameterPage extends WizardPage {
	private Text							fSourceFolder;
	private String							fSourceFolderStr;
	private Button							fBrowse;
	
	private Text							fName;
	
	private Button							fOverwrite;
	
	private TemplateFilesTableViewer		fFileTable;
	
	private TemplateParametersTreeViewer	fParamsTable;

	private TemplateInfo					fTemplate;
	
	private TemplateParameterProvider		fParameters;
	
	public SVTemplateParameterPage() {
		super("New SystemVerilog Class", "SystemVerilog Class", null);
		setDescription("Specify template parameters");
		fParameters = new TemplateParameterProvider();
	}

	public void setSourceFolder(String folder) {
		fSourceFolderStr = folder;
		
		if (fSourceFolder != null && !fSourceFolder.isDisposed()) {
			fSourceFolder.setText(fSourceFolderStr);
		}
		
		updateFilenamesDescription();
	}
	
	public String getSourceFolder() {
		return fSourceFolderStr;
	}
	
	public void setTemplate(TemplateInfo template) {
		// Flush state here
		fTemplate = template;
		
		updateFilenamesDescription();
		updateParameters();
	}
	
	public ITemplateParameterProvider getTagProcessor(boolean dont_expand_null_name) {
		TemplateParameterProvider tp = new TemplateParameterProvider(fParameters);
		
		// Don't replace ${name} if no name is specified
		if (!dont_expand_null_name) {
			if (!tp.hasTag("name")) {
				tp.setTag("name", "");
			}
		}
		
		// Add parameter values
		/*
		for (TemplateParameter p : fParamsTable.getParameters()) {
			tp.setTag(p.getName(), p.getValue());
		}
		 */

		return tp;
	}
	
	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		Label l;
		GridData gd;
		Group g;
		
		final Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		Composite src_c = new Composite(c, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		/** Select the destination location */
		l = new Label(src_c, SWT.NONE);
		l.setText("Source Folder:");
		
		fSourceFolder = new Text(src_c, SWT.BORDER);
		if (fSourceFolderStr != null) {
			fSourceFolder.setText(fSourceFolderStr);
		}
		fSourceFolder.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		fSourceFolder.addModifyListener(modifyListener);
		
		fBrowse = new Button(src_c, SWT.PUSH);
		fBrowse.setText("Browse");
		fBrowse.addSelectionListener(selectionListener);
		
		// Name
		l = new Label(src_c, SWT.NONE);
		l.setText("Name:");
		fName = new Text(src_c, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fName.setLayoutData(gd);
		fName.addModifyListener(modifyListener);
		
		// Overwrite Files
		l = new Label(src_c, SWT.NONE);
		l.setText("Overwrite Files:");
		fOverwrite = new Button(src_c, SWT.CHECK);
		fOverwrite.addSelectionListener(selectionListener);
		
		
		g = new Group(src_c, SWT.NONE);
		g.setText("Parameters");
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		
		fParamsTable = new TemplateParametersTreeViewer(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.heightHint = 100;
		fParamsTable.getTree().setLayoutData(gd);
		fParamsTable.addModifyListener(modifyListener);
		
		g = new Group(src_c, SWT.NONE);
		g.setText("Filenames");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.heightHint = 100;
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fFileTable = new TemplateFilesTableViewer(g, fParameters);
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fFileTable.getTable().setLayoutData(gd);

		setPageComplete(false);
		setControl(c);
		
		updateFilenamesDescription();
		
		fName.setFocus();
	}
	
	private void validate() {
		String err;
		
		setErrorMessage(null);
		
		if (fTemplate == null) {
			return;
		}
		
		if ((err = fFileTable.validate()) != null) {
			if (getErrorMessage() == null) {
				setErrorMessage(err);
			}
		}
		
		setPageComplete((getErrorMessage() == null));
	}
	
	private void updateFilenamesDescription() {
		String src_folder_str = (fSourceFolderStr != null)?fSourceFolderStr:"";
		
		if (fFileTable != null && !fFileTable.getTable().isDisposed()) {
			fFileTable.setSourceFolder(fSourceFolderStr);
			fFileTable.setTemplate(fTemplate);
		}
	
		/*
		if (fParamsTable != null && !fParamsTable.getTree().isDisposed()) {
			fParamsTable.setSourceFolder(fSourceFolderStr);
		}
		 */

		validate();
	}
	
	private void updateParameters() {
		if (fParamsTable != null && !fParamsTable.getTree().isDisposed()) {
			if (fTemplate != null) {
				fParamsTable.setParameters(fTemplate.getParameters());
			} else {
				fParamsTable.setParameters(null);
			}
		}
	}

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
	
	private ModifyListener modifyListener = new ModifyListener() {
		public void modifyText(ModifyEvent e) {
			if (e.widget == fSourceFolder) {
				fSourceFolderStr = fSourceFolder.getText();
				fFileTable.setSourceFolder(fSourceFolderStr);
			} else if (e.widget == fName) {
				fParameters.setTag("name", fName.getText());
			} else if (e.widget == fFileTable.getTable()) {
				
			}
			updateFilenamesDescription();
		}
	};
	
	private SelectionListener selectionListener = new SelectionListener() {
		
		public void widgetSelected(SelectionEvent e) {
			if (e.widget == fBrowse) {
				WorkspaceDirectoryDialog dlg = new WorkspaceDirectoryDialog(getShell());
				if (dlg.open() == Window.OK) {
					fSourceFolder.setText(dlg.getPath());
				}
			} else if (e.widget == fOverwrite) {
				boolean overwrite = fOverwrite.getSelection();
				if (fFileTable.getTable() != null && !fFileTable.getTable().isDisposed()) {
					fFileTable.setOverwriteFiles(overwrite);
				}
			}
			validate();
		}
		
		public void widgetDefaultSelected(SelectionEvent e) {}
	};

	/*
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
	 */

}
