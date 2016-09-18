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


package net.sf.sveditor.ui.wizards.templates;


import net.sf.sveditor.svt.core.SvtCorePlugin;
import net.sf.sveditor.svt.core.templates.TemplateCategory;
import net.sf.sveditor.svt.core.templates.TemplateInfo;
import net.sf.sveditor.svt.core.templates.WorkspaceTemplateRegistry;
import net.sf.sveditor.ui.doc.NDText;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;

public class SVTemplateSelectionPage extends WizardPage {
	
	private TreeViewer				fTemplateTree;
	private TemplateInfo			fTemplate;
	private TemplateCategory		fCategory;

	private NDText					fDescription;
	
	
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
		
		parent.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		SashForm sash = new SashForm(parent, SWT.VERTICAL);
		
		Composite top = new Composite(sash, SWT.BORDER);
		top.setLayout(new GridLayout());
		top.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		Composite src_c = new Composite(top, SWT.NONE);
		src_c.setLayout(new GridLayout(3, false));
		src_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		GridData gd;
		Group g;

		g = new Group(src_c, SWT.NONE);
		g.setText("A&vailable Templates");
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
		WorkspaceTemplateRegistry rgy = SvtCorePlugin.getDefault().getTemplateRgy();
		fTemplateTree.setInput(TemplateCategoriesNode.create(rgy));
		fTemplateTree.setSorter(SorterA);

		
		// TODO: move
		/*
		 */
	
		Composite bottom = new Composite(sash, SWT.BORDER);
		bottom.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		bottom.setLayoutData(gd);
		
		g = new Group(bottom, SWT.None);
		g.setText("Description");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		g.setLayout(new GridLayout());
		g.setLayoutData(gd);
		
		fDescription = new NDText(g, SWT.READ_ONLY+SWT.WRAP+SWT.V_SCROLL+SWT.H_SCROLL);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fDescription.setLayoutData(gd);

		setPageComplete(false);
		setControl(sash);
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

	private ViewerSorter SorterA = new ViewerSorter() {
		@Override
		public int compare(Viewer viewer, Object e1, Object e2) {
			if (e1 instanceof TemplateCategory && e2 instanceof TemplateCategory) {
				TemplateCategory c1 = (TemplateCategory)e1;
				TemplateCategory c2 = (TemplateCategory)e2;
				
				return c1.getName().compareTo(c2.getName());
			} else if (e1 instanceof TemplateInfo && e2 instanceof TemplateInfo) {
				TemplateInfo c1 = (TemplateInfo)e1;
				TemplateInfo c2 = (TemplateInfo)e2;
				
				return c1.getName().compareTo(c2.getName());
			} else {
				return super.compare(viewer, e1, e2);
			}
		}
	};
}
