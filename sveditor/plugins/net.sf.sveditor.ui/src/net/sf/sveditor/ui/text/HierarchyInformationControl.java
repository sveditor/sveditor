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
 *     Armond Paiva - repurposed from Objects Quick View to Outline Quick View
 *******************************************************************************/

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.views.hierarchy.HierarchyTreeContentProvider;
import net.sf.sveditor.ui.views.hierarchy.HierarchyTreeLabelProvider;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IElementComparer;
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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;

/**
 * Show outline in light-weight control.
 *
 * @since 2.1
 */
public class HierarchyInformationControl extends AbstractInformationControl {

	/**
	 * Creates a new system verilog outline information control.
	 *
	 * @param parent
	 * @param shellStyle
	 * @param treeStyle
	 * @param commandId
	 */
	public HierarchyInformationControl(Shell parent, int shellStyle, int treeStyle, String commandId) {
		super(parent, shellStyle, treeStyle, commandId, true);
	}

	
	protected FilteredTree fObjectTree ;
	protected PatternFilter fPatternFilter ;
	protected TreeViewer fTreeViewer ;
	protected SVDBClassDecl fClassDecl ;
	protected SVEditor fEditor ;

	@Override
	public void setFocus() {
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
		
		final Tree tree = fTreeViewer.getTree();
		
		GridData gd= new GridData(GridData.FILL_BOTH);
		gd.heightHint= tree.getItemHeight() * 20 ; // Initial height of dialog
		gd.widthHint = 600 ;					   // Initial width of dialog
		tree.setLayoutData(gd);
		
		fTreeViewer.setContentProvider(new HierarchyTreeContentProvider()) ;
		fTreeViewer.setLabelProvider(new HierarchyTreeLabelProvider()) ;
		fTreeViewer.setComparator(new ViewerComparator()) ;
		fTreeViewer.setComparer(new IElementComparer() {
			public int hashCode(Object element) {
				return element.hashCode();
			}
			public boolean equals(Object a, Object b) {
				// Just do a simple compare
				return (a == b);
			}
		});
		
		fTreeViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof HierarchyTreeNode) {
					HierarchyTreeNode n = (HierarchyTreeNode)sel.getFirstElement();
					SVDBItem item = n.getItemDecl() ;
					if(item != null) {
						try {
							SVEditorUtil.openEditor(item) ;
						} catch (PartInitException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					close() ;
				}
			}
		});		
		
		fTreeViewer.getTree().addKeyListener(new KeyListener() {
			public void keyPressed(KeyEvent e) {
				if(tree.getSelectionCount()==1 && (tree.getSelection()[0].getData() instanceof HierarchyTreeNode)) {
					HierarchyTreeNode n = (HierarchyTreeNode)tree.getSelection()[0].getData() ;
					SVDBItem item = n.getItemDecl() ;
					if(e.keyCode == SWT.CR){
						if(item != null) {
							try {
								SVEditorUtil.openEditor(item) ;
							} catch (PartInitException ex) {
								ex.printStackTrace();
							}
						}
						close() ;
					}
				}
			}
			public void keyReleased(KeyEvent e) { }
		}) ;

		return fTreeViewer;
	}


	@Override
	protected String getId() {
		return "net.sf.sveditor.ui.text.QuickOutline"; //$NON-NLS-1$
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void setInput(Object information) { 
		fEditor = null ;
		fClassDecl = null ;
		if(information != null && information instanceof ISVDBItemBase) {
			ISVDBItemBase itemBase = (ISVDBItemBase)information ;
			if(itemBase.getType() == SVDBItemType.ClassDecl) {
				fClassDecl = (SVDBClassDecl)itemBase ;
				IEditorPart editorPart = PlatformUI.getWorkbench().getActiveWorkbenchWindow()
												.getActivePage().getActiveEditor() ;
			    if(editorPart != null && editorPart instanceof SVEditor) {
			    	fEditor = (SVEditor)editorPart ;
					ClassHierarchyTreeFactory factory = new ClassHierarchyTreeFactory(fEditor.getIndexIterator()) ;
					HierarchyTreeNode root = factory.build(fClassDecl) ;
					while(root.getParent() != null) {
						root = root.getParent() ;
					}
					HierarchyTreeNode top = new HierarchyTreeNode(null, "") ;
					root.setParent(top) ;
					top.addChild(root) ;
					fTreeViewer.setInput(top) ;
					fTreeViewer.expandAll() ;
			    }
			}
		}
	}

}
