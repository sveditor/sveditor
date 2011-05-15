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


package net.sf.sveditor.ui.views.hierarchy;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

public class SVHierarchyView extends ViewPart implements SelectionListener {
	
	private TreeViewer					fClassTree;
	private TableViewer					fMemberList;
	/*
	private PageBook					fPageBook;
	private MessagePage					fNoSelPage;
	 */
	private HierarchyTreeNode			fTarget;
	private HierarchyTreeNode			fRoot;
	private SVTreeContentProvider		fMemberContentProvider;
	private Composite					fMemberComposite;
	private Label						fSelectedClass;
	private SVHierarchyViewerFilter		fViewerFilter;
	private Button						fShowInheritedMembers;
	/*
	private Button						fHideFields;
	private Button						fHideStatic;
	private Button						fHideNonPublic;
	
	private Button						fSortByDefiningType;
	 */

	@Override
	public void createPartControl(Composite parent) {

		/*
		fPageBook = new PageBook(parent, SWT.NONE);
		
		fNoSelPage = new MessagePage();
		fNoSelPage.setMessage("No current selection...");
		 */
		
		SashForm sash = new SashForm(parent, SWT.VERTICAL);

		GridLayout gl;
		gl = new GridLayout();
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		Composite class_c = new Composite(sash, SWT.NONE);
		class_c.setLayout(gl);
		class_c.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fClassTree = new TreeViewer(class_c);
		fClassTree.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fClassTree.setContentProvider(new HierarchyTreeContentProvider());
		fClassTree.setLabelProvider(new HierarchyTreeLabelProvider());
		
		// Propagate the class selection to the member list
		fClassTree.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				Object elem = sel.getFirstElement();
				if (elem instanceof HierarchyTreeNode) {
					fViewerFilter.setTarget((HierarchyTreeNode)elem);
					fSelectedClass.setText(((HierarchyTreeNode)elem).getName());
					fMemberList.setInput(((HierarchyTreeNode)elem).getItemDecl());
				} else {
					fMemberList.setInput(null);
					fSelectedClass.setText("");
					fViewerFilter.setTarget(null);
				}
				fMemberComposite.layout(true, true);
			}
		});
		fClassTree.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof HierarchyTreeNode) {
					HierarchyTreeNode n = (HierarchyTreeNode)sel.getFirstElement();
					if (n.getItemDecl() != null) {
						try {
							SVEditorUtil.openEditor(n.getItemDecl());
						} catch (PartInitException e) {
							e.printStackTrace();
						}
					}
				}
			}
		});

		sash.setLayoutData(
				new GridData(SWT.FILL, SWT.CENTER, true, false));
		
		fMemberComposite = new Composite(sash, SWT.NO_TRIM);
		fMemberComposite.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		gl = new GridLayout();
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		fMemberComposite.setLayout(gl);

		Composite member_action_bar = new Composite(fMemberComposite, SWT.NONE);
		gl = new GridLayout(2, true);
		gl.marginHeight = 0;
		/*
		gl.marginWidth = 0;
		gl.marginLeft  = 2;
		 */
		member_action_bar.setLayout(gl);
		member_action_bar.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, false));
				
		fSelectedClass = new Label(member_action_bar, SWT.NONE);

		Composite member_button_bar = new Composite(member_action_bar, SWT.NONE);
		GridData gd = new GridData(SWT.FILL, SWT.FILL, false, false);
		gd.heightHint = 16;
		member_button_bar.setLayoutData(gd);
		gl = new GridLayout(5, true);
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		member_button_bar.setLayout(gl);
		
		/*
		fShowInheritedMembers = new Button(member_button_bar, SWT.TOGGLE+SWT.FLAT);
		fShowInheritedMembers.setImage(SVUiPlugin.getImage("/icons/elcl16/inher_co.gif"));
		fShowInheritedMembers.addSelectionListener(this);
		 */

		fMemberContentProvider = new SVTreeContentProvider();
		fMemberList = new TableViewer(fMemberComposite);
		fMemberList.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fMemberList.setContentProvider(fMemberContentProvider);
		fMemberList.setLabelProvider(new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()));
		fMemberList.addDoubleClickListener(new IDoubleClickListener() {
			
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof SVDBItem) {
					try {
						SVEditorUtil.openEditor((ISVDBItemBase)sel.getFirstElement());
					} catch (PartInitException e) {
						e.printStackTrace();
					}
				}
			}
		});
		fViewerFilter = new SVHierarchyViewerFilter();
		fMemberList.addFilter(fViewerFilter);
	}
	
	public void widgetDefaultSelected(SelectionEvent e) {}

	public void widgetSelected(SelectionEvent e) {
		if (e.item == fShowInheritedMembers) {
			
		}
	}

	public void setTarget(HierarchyTreeNode target) {
		fTarget = target;
		fRoot = target;
		fViewerFilter.setTarget(fTarget);
		
		while (fRoot.getParent() != null) {
			fRoot = fRoot.getParent();
		}
		// Add an empty node to contain the tree
		target = new HierarchyTreeNode(null, "");
		fRoot.setParent(target);
		target.addChild(fRoot);
		fRoot = target;
		
		Display.getDefault().asyncExec(new Runnable() {
			
			public void run() {
				fClassTree.setInput(fRoot);
				fClassTree.setSelection(new StructuredSelection(fTarget), true);
				fClassTree.expandToLevel(fTarget, 1);
			}
		});
	}

	@Override
	public void setFocus() {}
}


