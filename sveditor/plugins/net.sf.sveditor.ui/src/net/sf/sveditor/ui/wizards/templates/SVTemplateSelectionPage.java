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
import net.sf.sveditor.core.templates.TemplateCategory;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateRegistry;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class SVTemplateSelectionPage extends WizardPage {
	
	private TreeViewer				fTemplateTree;
	private TemplateInfo			fTemplate;
	private TemplateCategory		fCategory;
	
	private Text					fDescription;
	
	
	public SVTemplateSelectionPage() {
		super("New SystemVerilog Methodology Component", "", null);
		setDescription("Create a new SystemVerilog methodology component");
	}
	
	public TemplateInfo getTemplate() {
		return fTemplate;
	}
	
	//
	// Source Folder
	// 
	public void createControl(Composite parent) {
		Label l;
		
		parent.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		parent.setBackground(Display.getDefault().getSystemColor(SWT.COLOR_BLUE));
		
		final Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
//		c.setBackground(Display.getDefault().getSystemColor(SWT.COLOR_RED));
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		Composite src_c = new Composite(c, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		GridData gd;
		Group g;

		g = new Group(src_c, SWT.NONE);
		g.setText("Available Templates");
		g.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		
		fTemplateTree = new TreeViewer(g);
		fTemplateTree.setContentProvider(new TemplateCategoriesContentProvider());
		fTemplateTree.setLabelProvider(new TemplateCategoriesLabelProvider());
		fTemplateTree.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fTemplateTree.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				templateSelectionChanged(event);
			}
		});
		TemplateRegistry rgy = SVCorePlugin.getDefault().getTemplateRgy();
		fTemplateTree.setInput(TemplateCategoriesNode.create(rgy));

		
		// TODO: move
		/*
		 */
		
		g = new Group(c, SWT.None);
		g.setText("Description");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		g.setLayout(new GridLayout());
		g.setLayoutData(gd);
		
		fDescription = new Text(g, SWT.READ_ONLY);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fDescription.setLayoutData(gd);

//		fName.setFocus();
		//loadCategoryList();
		//updateFilenamesDescription();
		
		setPageComplete(false);
		setControl(c);
	}
	
	private void templateSelectionChanged(SelectionChangedEvent event) {
		IStructuredSelection sel = (IStructuredSelection)event.getSelection();
		fTemplate = null;
		fCategory = null;
		
		if (sel.getFirstElement() instanceof TemplateInfo) {
			fTemplate = (TemplateInfo)sel.getFirstElement();
		} else if (sel.getFirstElement() instanceof TemplateCategory) {
			fCategory = (TemplateCategory)sel.getFirstElement();
		}
		
		validate();
	}

	/*
	 */
	
	/*
	@SuppressWarnings("rawtypes")
	private void loadCategoryList() {
		TemplateRegistry rgy = SVCorePlugin.getDefault().getTemplateRgy();
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
	 */
	

	/*
	@SuppressWarnings("rawtypes")
	private void updateTemplateList() {
		TemplateRegistry rgy = SVCorePlugin.getDefault().getTemplateRgy();
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
		
		updateFilenamesDescription();
	}
	 */
	
	private void validate() {
		setErrorMessage(null);

		if (fCategory != null) {
			fDescription.setText(fCategory.getDescription());
		} else if (fTemplate != null) {
			fDescription.setText(fTemplate.getDescription());
		} else {
			fDescription.setText("");
		}
		
		if (getErrorMessage() == null) {
			if (fTemplate == null) {
				setErrorMessage("No template selected");
			}
		}
		
		setPageComplete((getErrorMessage() == null));
	}

	/*
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
	 */
	
	private void debug(String msg) {
		// System.out.println(msg);
	}
}
