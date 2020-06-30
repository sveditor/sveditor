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
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package net.sf.sveditor.ui.views.objects;

import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVEditorUtil;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.objects.ObjectsTreeNode;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;
import org.eclipse.ui.part.ViewPart;

public class SVObjectsView extends ViewPart implements SelectionListener {
	
	private FilteredTree	     		fObjectTree;
	private TreeViewer				    fTreeViewer;
	private PatternFilter				fPatternFilter;
	private ObjectsViewContentProvider 	fContentProvider;
	
	@Override
	public void createPartControl(Composite parent) {
		
		GridLayout gl;
		
		gl = new GridLayout();
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		
		Composite class_c = new Composite(parent, SWT.NONE);
		class_c.setLayout(gl);
		class_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fPatternFilter =  new PatternFilter() ;
		
		fObjectTree = new FilteredTree(class_c, SWT.H_SCROLL|SWT.V_SCROLL, fPatternFilter,true);
		
		fTreeViewer = fObjectTree.getViewer() ;
		fTreeViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		fTreeViewer.setContentProvider(fContentProvider = new ObjectsViewContentProvider());
		fTreeViewer.setLabelProvider(new ObjectsLabelProvider());
		fTreeViewer.setInput(SVCorePlugin.getDefault().getSVDBIndexRegistry());
		fTreeViewer.setComparator(new ViewerComparator()) ;
		
		fTreeViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof ObjectsTreeNode) {
					ObjectsTreeNode n = (ObjectsTreeNode)sel.getFirstElement();
					// First level nodes for object types get expanded on double click
					if(n == fContentProvider.getModulesNode() || 
					   n == fContentProvider.getInterfacesNode() ||
					   n == fContentProvider.getPackagesNode()) {
						fTreeViewer.setExpandedState(n, !fTreeViewer.getExpandedState(n)) ;
					// Packages toggle expanded state
					} else if(n.getItemDecl().getType() == SVDBItemType.PackageDecl) {
						fTreeViewer.setExpandedState(n, !fTreeViewer.getExpandedState(n)) ;
					// Otherwise, try to open associated file
					} else {
						if (n.getItemDecl() != null) {
							try {
								if( n.getItemDecl() != null && n.getItemDecl().getFile() != null) {
									SVEditorUtil.openEditor(n.getItemDecl().getFile()) ;
								}
							} catch (PartInitException e) {
								e.printStackTrace();
							}
						}
					}
				}
			}
		});

	}

	
	@Override
	public void init(IViewSite site) throws PartInitException {
		super.init(site);
		
		IToolBarManager tbm = site.getActionBars().getToolBarManager() ;
		
		tbm.add( new Action("Collapse All", Action.AS_PUSH_BUTTON) { 
					{ setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
						.getImageDescriptor(ISharedImages.IMG_ELCL_COLLAPSEALL)) ; } 
					public void run() { fTreeViewer.collapseAll() ; }}) ;
		
		tbm.add( new Action("Expand Interfaces", Action.AS_PUSH_BUTTON) {
					{ setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.InterfaceDecl)) ; } 
					public void run() { 
						if(fContentProvider.getInterfacesNode() != null) {
							fTreeViewer.collapseAll() ; 
					        fTreeViewer.expandToLevel(fContentProvider.getInterfacesNode(), TreeViewer.ALL_LEVELS) ; 
						}}}) ;
		
		tbm.add( new Action("Expand Modules", Action.AS_PUSH_BUTTON) { 
					{ setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.ModuleDecl)) ; } 
					public void run() { 
						if(fContentProvider.getModulesNode() != null) {
							fTreeViewer.collapseAll() ; 
					        fTreeViewer.expandToLevel(fContentProvider.getModulesNode(), TreeViewer.ALL_LEVELS) ; 
						}}}) ;
		
		tbm.add( new Action("Expand Packages", Action.AS_PUSH_BUTTON) { 
					{ setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.PackageDecl)) ; } 
					public void run() { 
						if(fContentProvider.getPackagesNode() != null) {
							fTreeViewer.collapseAll() ; 
					        fTreeViewer.expandToLevel(fContentProvider.getPackagesNode(), 1) ;
						}}}) ;
		
		tbm.add( new Action("Expand Classes", Action.AS_PUSH_BUTTON) { 
					{ setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.ClassDecl)) ; } 
					public void run() { 
						if(fContentProvider.getPackagesNode() != null) {
							fTreeViewer.collapseAll() ; 
					        fTreeViewer.expandToLevel(fContentProvider.getPackagesNode(), TreeViewer.ALL_LEVELS) ; 
						}}}) ;
		
		
		tbm.add( new Action("Reload", Action.AS_PUSH_BUTTON) { 
					{ setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
						.getImageDescriptor(ISharedImages.IMG_TOOL_REDO)) ; } 
					public void run() { 
						fTreeViewer.setInput(SVCorePlugin.getDefault().getSVDBIndexRegistry()); }}) ;
		
	}
	
	public void widgetDefaultSelected(SelectionEvent e) {}

	public void widgetSelected(SelectionEvent e) {}
	
	public void setFocus() {}
	
}


