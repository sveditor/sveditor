package net.sf.sveditor.ui.text;

/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed from JDT for SVEditor Objects Quick View
 *******************************************************************************/

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.objects.ObjectsTreeNode;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.views.objects.ObjectsLabelProvider;
import net.sf.sveditor.ui.views.objects.ObjectsViewContentProvider;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;

/**
 * Show outline in light-weight control.
 *
 * @since 2.1
 */
public class ObjectsInformationControl extends AbstractInformationControl {

	/**
	 * Creates a new Java outline information control.
	 *
	 * @param parent
	 * @param shellStyle
	 * @param treeStyle
	 * @param commandId
	 */
	public ObjectsInformationControl(Shell parent, int shellStyle, int treeStyle, String commandId) {
		super(parent, shellStyle, treeStyle, commandId, true);
	}

	
	protected FilteredTree fObjectTree ;
	protected PatternFilter fPatternFilter ;
	protected TreeViewer fTreeViewer ;
	protected ObjectsViewContentProvider fContentProvider ;

	@Override
	public void setFocus() {
	  super.setFocus() ;
	  fObjectTree.getFilterControl().setFocus() ;
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	protected TreeViewer createTreeViewer(Composite parent, int style) {
		
		fPatternFilter = new PatternFilter() ;

		fObjectTree = new FilteredTree(parent, SWT.H_SCROLL, fPatternFilter, true) ;
		fTreeViewer = fObjectTree.getViewer() ;
		fContentProvider = new ObjectsViewContentProvider() ;
		
		final Tree tree = fTreeViewer.getTree();
		
		GridData gd= new GridData(GridData.FILL_BOTH);
		gd.heightHint= tree.getItemHeight() * 20 ; // Initial height of dialog
		gd.widthHint = 600 ;					   // Initial width of dialog
		tree.setLayoutData(gd);
		
		fTreeViewer.setContentProvider(fContentProvider) ;
		fTreeViewer.setLabelProvider(new ObjectsLabelProvider());
		fTreeViewer.setInput(SVCorePlugin.getDefault().getSVDBIndexRegistry());
		fTreeViewer.setComparator(new ViewerComparator()) ;
		
		addKeyListeners() ;
		
		
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

		return fTreeViewer;
	}

	private void addKeyListeners() {
		final Tree tree = fTreeViewer.getTree() ;
		tree.addKeyListener(new KeyListener() {
			@Override
			public void keyReleased(KeyEvent e) {}
			@Override
			public void keyPressed(KeyEvent e) {
				if(tree.getSelectionCount()==1 && (tree.getSelection()[0].getData() instanceof ObjectsTreeNode)) {
					ObjectsTreeNode n = (ObjectsTreeNode)tree.getSelection()[0].getData() ;
					if(e.keyCode == SWT.CR) {
						// First level nodes for object types get expanded
						if(n == fContentProvider.getModulesNode() ||
						   n == fContentProvider.getInterfacesNode() ||
						   n == fContentProvider.getPackagesNode()) {
							fTreeViewer.setExpandedState(n, !fTreeViewer.getExpandedState(n)) ;
						// Packages toggle expanded state
						} else if(n.getItemDecl().getType() == SVDBItemType.PackageDecl) {
							fTreeViewer.setExpandedState(n, !fTreeViewer.getExpandedState(n)) ;
						// Otherwise, try to open associated file
						} else if(n.getItemDecl() != null && n.getItemDecl().getFile() != null) {
							try {
								SVEditorUtil.openEditor(n.getItemDecl().getFile()) ;
							} catch (PartInitException e1) {
								// TODO Auto-generated catch block
								e1.printStackTrace();
							}
						}
					}
					else if(e.keyCode == SWT.ARROW_RIGHT) {
						// First level nodes for object types get expanded
						if(n == fContentProvider.getModulesNode() ||
						   n == fContentProvider.getInterfacesNode() ||
						   n == fContentProvider.getPackagesNode()) {
							fTreeViewer.setExpandedState(n, true) ;
						// Packages toggle expanded state
						} else if(n.getItemDecl().getType() == SVDBItemType.PackageDecl) {
							fTreeViewer.setExpandedState(n, true) ; 
						// Otherwise, at leaf, do nothing
						}
					}
					else if(e.keyCode == SWT.ARROW_LEFT) {
						// First level nodes for object types get collapsed
						if(n == fContentProvider.getModulesNode() ||
						   n == fContentProvider.getInterfacesNode() ||
						   n == fContentProvider.getPackagesNode()) {
							fTreeViewer.setExpandedState(n, false) ;
						// Packages get collapsed
						} else if(n.getItemDecl().getType() == SVDBItemType.PackageDecl) {
							fTreeViewer.setExpandedState(n, false) ; 
						// Otherwise, at leaf, collapse parent node
						} else if(n.getItemDecl() != null && n.getParent() != null) {
							fTreeViewer.setExpandedState(n.getParent(), false) ;
						}
					}
// Hmm... this still closes the dialog.					
//					if(e.keyCode == SWT.ESC) {
//						// Move focus to the search entry
//						// Banging ESC again there will close the dialog
//						fObjectTree.getFilterControl().setFocus() ;
//					}
				}
			}
		}) ;
		
	}

	@Override
	protected String getId() {
		return "net.sf.sveditor.ui.text.QuickObjects"; //$NON-NLS-1$
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void setInput(Object information) { }


}
