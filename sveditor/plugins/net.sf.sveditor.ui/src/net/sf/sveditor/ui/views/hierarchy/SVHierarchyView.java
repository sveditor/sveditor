/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.views.hierarchy;

import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.internal.ui.viewers.FindElementDialog;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBPackageDecl;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.eclipse.hdt.sveditor.core.hierarchy.HierarchyTreeNode;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IElementComparer;
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
	private ISVDBIndexIterator			fIndexIt;
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
		fClassTree.setSorter(new SVHierarchyViewerSorter());
		
		// Propagate the class selection to the member list
		fClassTree.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				Object elem = sel.getFirstElement();
				if (elem instanceof HierarchyTreeNode) {
					HierarchyTreeNode hn = (HierarchyTreeNode)elem;
					fViewerFilter.setTarget(hn);
					fSelectedClass.setText(hn.getName());
					if (hn.getAltItemDecl() != null) {
						SVDBDeclCacheItem ci = hn.getAltItemDecl();
						if (ci.getType() == SVDBItemType.PackageDecl) {
							List<SVDBDeclCacheItem> pkg_i = fIndexIt.findPackageDecl(
									new NullProgressMonitor(), ci);
							fMemberList.setInput(pkg_i);
						} else if (ci.getType() == SVDBItemType.ImportItem) {
							String pkg_name = ci.getName();
							int idx;
							
							if ((idx=pkg_name.indexOf("::")) != -1) {
								pkg_name = pkg_name.substring(0, idx);
							}
							
							List<SVDBDeclCacheItem> pkgs = fIndexIt.findGlobalScopeDecl(
									new NullProgressMonitor(), pkg_name, 
									new SVDBFindByNameMatcher(SVDBItemType.PackageDecl));
							
							if (pkgs.size() > 0) {
								List<SVDBDeclCacheItem> pkg_i = fIndexIt.findPackageDecl(
										new NullProgressMonitor(), pkgs.get(0));
								fMemberList.setInput(pkg_i);
							} else {
								fMemberList.setInput(null);
							}
						} else {
							fMemberList.setInput(null);
						}
					} else if (hn.getItemDecl() != null) {
						ISVDBItemBase it = hn.getItemDecl();
						if (it.getType() == SVDBItemType.ClassDecl) {
							fMemberList.setInput(it);
						} else if (it.getType().isElemOf(SVDBItemType.ModIfcInstItem, SVDBItemType.VarDeclItem)) {
							// Set the context to the parent item
							ISVDBItemBase type = hn.getItemType();
							fMemberList.setInput(type);
						} else {
							fMemberList.setInput(it);
						}
					} else {
						fMemberList.setInput(hn.getItemDecl());
					}
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
			
					ISVDBItemBase it = null;
					
					if (n.getAltItemDecl() != null) {
						it = n.getAltItemDecl().getSVDBItem();
					} else if (n.getItemDecl() != null) {
						it = n.getItemDecl();
					}
					
					if (it != null) {
						try {
							SVEditorUtil.openEditor(it);
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
		fMemberList.setComparer(new IElementComparer() {
			
			public int hashCode(Object element) {
				return element.hashCode();
			}
			
			public boolean equals(Object a, Object b) {
				return (a == b);
			}
		});
		
		fMemberList.addDoubleClickListener(new IDoubleClickListener() {
			
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof ISVDBItemBase) {
					try {
						SVEditorUtil.openEditor((ISVDBItemBase)sel.getFirstElement());
					} catch (PartInitException e) {
						e.printStackTrace();
					}
				} else if (sel.getFirstElement() instanceof SVDBDeclCacheItem) {
					SVDBDeclCacheItem dci = (SVDBDeclCacheItem)sel.getFirstElement();
					
					try {
						SVEditorUtil.openEditor(dci.getSVDBItem());
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

	public void setTarget(
			HierarchyTreeNode 	target,
			ISVDBIndexIterator	index_it) {
		fTarget = target;
		fIndexIt = index_it;
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


