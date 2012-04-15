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


import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.SortUtils;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateProcessor;
import net.sf.sveditor.core.templates.TemplateRegistry;
import net.sf.sveditor.core.text.TagProcessor;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.WorkspaceDirectoryDialog;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;

public class NewSVMethodologyClassWizardBasicsPage extends WizardPage {
	private Text					fSourceFolder;
	private String					fSourceFolderStr;
	
	private Text					fName;
	private String					fNameStr;
	
	private Combo					fCategoryCombo;	
	private Combo					fTemplateCombo;
	private TemplateInfo			fTemplate;
	
	private TableViewer				fFileTable;
	private List<String>			fFileNames;
	
	
	public NewSVMethodologyClassWizardBasicsPage() {
		super("New SystemVerilog Methodology Component", "", null);
		setDescription("Create a new SystemVerilog methodology component");
		fFileNames = new ArrayList<String>();
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
	
	public TemplateInfo getTemplate() {
		return fTemplate;
	}
	
	public List<String> getFileNames() {
		return fFileNames;
	}
	
	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		Label l;
		
		fNameStr = "";
		
		final Composite c = new Composite(parent, SWT.NONE);
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
				validate();
			}
		});
		final Button sf_browse = new Button(src_c, SWT.PUSH);
		sf_browse.setText("Browse");
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
		l.setText("Name:");
		
		fName = new Text(src_c, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fName.setLayoutData(gd);
		fName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fNameStr = fName.getText();
				updateFilenames();
				validate();
			}
		});

		l = new Label(src_c, SWT.NONE);
		l.setText("Category:");
		
		fCategoryCombo = new Combo(src_c, SWT.READ_ONLY);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fCategoryCombo.setLayoutData(gd);
		fCategoryCombo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				updateTemplateList();
				fTemplateCombo.select(0);
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		l = new Label(src_c, SWT.NONE);
		l.setText("Class Template:");
		
		fTemplateCombo = new Combo(src_c, SWT.READ_ONLY);
		gd = new GridData(SWT.FILL, SWT.FILL, true, false);
		gd.horizontalSpan = 2;
		fTemplateCombo.setLayoutData(gd);
		fTemplateCombo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				TemplateRegistry rgy = TemplateRegistry.getDefault();
				List<String> category_ids = rgy.getCategoryIDs();
				String id = category_ids.get(fCategoryCombo.getSelectionIndex());
				List<TemplateInfo> templates = rgy.getTemplates(id);
				fTemplate = templates.get(fTemplateCombo.getSelectionIndex());
				updateFilenames();
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		Group g = new Group(src_c, SWT.NONE);
		g.setText("Filenames");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.heightHint = 100;
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fFileTable = new TableViewer(g);
		fFileTable.getTable().setHeaderVisible(true);
		TableColumn err = new TableColumn(fFileTable.getTable(), SWT.LEFT, 0);
		err.setText("Status");
		err.setWidth(50);
		TableColumn file = new TableColumn(fFileTable.getTable(), SWT.LEFT, 1);
		file.setText("Filename");
		file.setWidth(400);
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fFileTable.getTable().setLayoutData(gd);
		fFileTable.setContentProvider(new IStructuredContentProvider() {
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
			public void dispose() {}
			
			@SuppressWarnings("rawtypes")
			public Object[] getElements(Object inputElement) {
				return ((List)inputElement).toArray();
			}
		});
		fFileTable.setLabelProvider(new ITableLabelProvider() {
			
			public void removeListener(ILabelProviderListener listener) {}
			
			public boolean isLabelProperty(Object element, String property) {
				return false;
			}
			
			public void dispose() {}
			
			public void addListener(ILabelProviderListener listener) {}
			
			public String getColumnText(Object element, int columnIndex) {
				if (columnIndex == 1) {
					// Filename column
					return element.toString();
				} else {
					return null;
				}
			}
			
			public Image getColumnImage(Object element, int columnIndex) {
				if (columnIndex == 0) {
					IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);
					String filename = element.toString();
					IFile file = c.getFile(new Path(filename));
					
					if (file.exists()) {
						return SVUiPlugin.getImage("/icons/eview16/error.gif");
					} else {
						return SVUiPlugin.getImage("/icons/eview16/signed_yes.gif");
					}
				} else {
					return null;
				}
			}
		});
		fFileTable.setInput(fFileNames);

		fName.setFocus();
		loadCategoryList();
		updateFilenames();
		
		setPageComplete(false);
		setControl(c);
	}

	private void updateFilenames() {
		TagProcessor tp = getTagProcessor(true);
		
		fFileNames = new ArrayList<String>();
		
		fFileNames.addAll(TemplateProcessor.getOutputFiles(fTemplate, tp));

		fFileTable.setInput(fFileNames);
	}
	
	@SuppressWarnings("rawtypes")
	private void loadCategoryList() {
		TemplateRegistry rgy = TemplateRegistry.getDefault();
		List<String> names = new ArrayList<String>();
		names.addAll(rgy.getCategoryNames());
		
		SortUtils.sort(names, new Comparator() {
			public int compare(Object o1, Object o2) {
				return ((String)o1).compareTo((String)o2);
			}
		}, true);
		
		
		fCategoryCombo.setItems(names.toArray(new String[names.size()]));
		fCategoryCombo.select(0);
		updateTemplateList();
	}
	
	public TagProcessor getTagProcessor(boolean dont_expand_null_name) {
		TagProcessor tp = new TagProcessor();
		
		// Don't replace ${name} if no name is specified
		if (!dont_expand_null_name || !fNameStr.trim().equals("")) {
			tp.appendTag("name", fNameStr);
		}

		return tp;
	}
	
	@SuppressWarnings("rawtypes")
	private void updateTemplateList() {
		TemplateRegistry rgy = 
			TemplateRegistry.getDefault();
		String sel = fCategoryCombo.getText();
		int category_idx = rgy.getCategoryNames().indexOf(sel);
		
		String id = rgy.getCategoryIDs().get(category_idx);
		
		List<TemplateInfo> templates = new ArrayList<TemplateInfo>(rgy.getTemplates(id));
		SortUtils.sort(templates, new Comparator() {
			public int compare(Object o1, Object o2) {
				TemplateInfo i1 = (TemplateInfo)o1;
				TemplateInfo i2 = (TemplateInfo)o2;
				return (i1.getName().compareTo(i2.getName()));
			}
		}, true);
		
		debug("Category: " + id);
		
		String items[] = new String[templates.size()];
		for (int i=0; i<templates.size(); i++) {
			debug("    Template: " + templates.get(i).getName());
			items[i] = templates.get(i).getName();
		}
		fTemplateCombo.setItems(items);
		fTemplateCombo.select(0);
		fTemplate = templates.get(0);
		
		updateFilenames();
	}
	
	private void validate() {
		setErrorMessage(null);
		if (!SVCharacter.isSVIdentifier(fNameStr)) {
			setErrorMessage("Invalid class name format");
		}
		
		IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);
		if (c != null) {
			// TODO: validate all proposed files to ensure none exist
			fTemplate.getTemplates();
			for (String filename : getFileNames()) {
				IFile file = c.getFile(new Path(filename));
				if (file.exists()) {
					setErrorMessage("File \"" + filename + "\" exists");
				}
			}
		} else {
			setErrorMessage("Directory \"" + 
					fSourceFolderStr + "\" does not exist");
		}
		
		setPageComplete((getErrorMessage() == null));
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
	
	private void debug(String msg) {
		// System.out.println(msg);
	}
}
