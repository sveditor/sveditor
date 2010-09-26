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


package net.sf.sveditor.ui.editor.actions;

import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;
import net.sf.sveditor.ui.views.hierarchy.HierarchyTreeFactory;
import net.sf.sveditor.ui.views.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.ui.views.hierarchy.SVHierarchyView;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenTypeHierarchyAction extends TextEditorAction {
	
	public OpenTypeHierarchyAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "OpenTypeHierarchy.", editor);
	}

	@Override
	public void run() {
		IDocument doc = getTextEditor().getDocumentProvider().getDocument(
				getTextEditor().getEditorInput());
		ITextSelection sel = getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();

		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		SVExprScanner			expr_scanner = new SVExprScanner();
		
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
		
		if (expr_ctxt.fLeaf != null && 
				(expr_ctxt.fTrigger == null || expr_ctxt.fTrigger.equals(""))) {
			SVDBFindNamedModIfcClassIfc finder_c = new SVDBFindNamedModIfcClassIfc(
					((SVEditor)getTextEditor()).getIndexIterator());
			
			List<SVDBModIfcClassDecl> result = finder_c.find(expr_ctxt.fLeaf); 
			SVDBModIfcClassDecl cls = (result != null && result.size() > 0)?result.get(0):null; 
			
			if (cls != null) {
				HierarchyTreeFactory factory = new HierarchyTreeFactory(
						((SVEditor)getTextEditor()).getIndexIterator());

				// Iterate up the inheritance tree and prune any 
				// branches that are not related to the target class
				HierarchyTreeNode n = factory.build(cls);
				HierarchyTreeNode nt = n, p;
				
				while ((p = nt.getParent()) != null) {
					for (int i=0; i<p.getChildren().size(); i++) {
						if (p.getChildren().get(i) != nt) {
							p.getChildren().remove(i);
							i--;
						}
					}
					nt = nt.getParent();
				}

				try {
					IWorkbench workbench = PlatformUI.getWorkbench();
					IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
					IViewPart view;
					if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".hierarchyView")) == null) {
						// Create the view
						view = page.showView(SVUiPlugin.PLUGIN_ID + ".hierarchyView");
					}
					
					page.activate(view);
					
					((SVHierarchyView)view).setTarget(n);
						
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		
	}
	
	/*
	private void print_down(int indent, HierarchyTreeNode node) {
		String indent_s = "";
		for (int i=0; i<indent; i++) {
			indent_s += "  ";
		}
		
		System.out.println(indent_s + "node: " + 
				node.getName() + " " +
				((node.getClassDecl() != null)?node.getClassDecl().getName():"null"));
		for (HierarchyTreeNode n : node.getChildren()) {
			print_down(indent+1, n);
		}
	}
	 */
	
	private ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		if (getTextEditor() != null) {
			ISelection sel_o = 
				getTextEditor().getSelectionProvider().getSelection();
			if (sel_o != null && sel_o instanceof ITextSelection) {
				sel = (ITextSelection)sel_o;
			} 
		}
		
		return sel;
	}

}
