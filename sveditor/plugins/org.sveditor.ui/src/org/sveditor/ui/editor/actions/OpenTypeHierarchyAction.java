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


package org.sveditor.ui.editor.actions;

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.ResourceBundle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import org.sveditor.core.db.search.SVDBFindNamedPackage;
import org.sveditor.core.expr_utils.SVExprContext;
import org.sveditor.core.expr_utils.SVExprScanner;
import org.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import org.sveditor.core.hierarchy.HierarchyTreeNode;
import org.sveditor.core.hierarchy.ModuleHierarchyTreeFactory;
import org.sveditor.core.hierarchy.PackageHierarchyTreeFactory;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

import org.sveditor.ui.SVUiPlugin;
import org.sveditor.ui.editor.SVEditor;
import org.sveditor.ui.scanutils.SVDocumentTextScanner;
import org.sveditor.ui.views.hierarchy.SVHierarchyView;

public class OpenTypeHierarchyAction extends TextEditorAction {
	private IWorkbench				fWorkbench;
	private SVDocumentTextScanner	fScanner;
	
	public OpenTypeHierarchyAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "OpenTypeHierarchy.", editor);
		fWorkbench = editor.getEditorSite().getWorkbenchWindow().getWorkbench();
	}

	@Override
	public void run() {
		IDocument doc = getTextEditor().getDocumentProvider().getDocument(
				getTextEditor().getEditorInput());
		ITextSelection sel = getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();

		fScanner = new SVDocumentTextScanner(doc, offset);
		
		
		try {
			fWorkbench.getProgressService().run(false, false, fOpenHierarchy);
		} catch (InvocationTargetException e) {
		} catch (InterruptedException e) {
		}
	}
	
	private IRunnableWithProgress fOpenHierarchy = new IRunnableWithProgress() {
		
		public void run(IProgressMonitor monitor) throws InvocationTargetException,
				InterruptedException {
			monitor.beginTask("Open Type Hierarchy", 4);
			SVExprScanner			expr_scanner = new SVExprScanner();
			SVExprContext expr_ctxt = expr_scanner.extractExprContext(fScanner, true);
			
			monitor.worked(1);
			if (expr_ctxt.fLeaf != null && 
					(expr_ctxt.fTrigger == null || expr_ctxt.fTrigger.equals(""))) {
				ISVDBIndexIterator index_it = ((SVEditor)getTextEditor()).getIndexIterator();
				SVDBFindNamedModIfcClassIfc finder_c = new SVDBFindNamedModIfcClassIfc(index_it);
				
				List<SVDBDeclCacheItem> result = finder_c.findItems(expr_ctxt.fLeaf); 
				
				SVDBDeclCacheItem cls = null;
				if (result != null && result.size() > 0) {
					cls = result.get(0);
				} else {
					// Try again, this time looking for packages
					SVDBFindNamedPackage finder_p = new SVDBFindNamedPackage(
						((SVEditor)getTextEditor()).getIndexIterator());
					result = finder_p.find(expr_ctxt.fLeaf);
					
					if (result != null && result.size() > 0) {
						cls = result.get(0);
					}
				}

				monitor.worked(1);

				if (cls != null) {
					HierarchyTreeNode target = null;
					if (cls.getType() == SVDBItemType.ClassDecl) {
						ClassHierarchyTreeFactory factory = new ClassHierarchyTreeFactory(
								((SVEditor)getTextEditor()).getIndexIterator());

						target = factory.build(cls);
					} else if (cls.getType() == SVDBItemType.ModuleDecl) {
						ModuleHierarchyTreeFactory factory = new ModuleHierarchyTreeFactory(
								((SVEditor)getTextEditor()).getIndexIterator());
						
						target = factory.build(cls);
					} else if (cls.getType() == SVDBItemType.PackageDecl) {
						PackageHierarchyTreeFactory factory = new PackageHierarchyTreeFactory(
								((SVEditor)getTextEditor()).getIndexIterator());
						target = factory.build(cls);
					}
					
					monitor.worked(1);
					
					if (target != null) {
						try {
							IWorkbench workbench = PlatformUI.getWorkbench();
							IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
							IViewPart view;
							if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".hierarchyView")) == null) {
								// Create the view
								view = page.showView(SVUiPlugin.PLUGIN_ID + ".hierarchyView");
							}

							page.activate(view);

							((SVHierarchyView)view).setTarget(target, index_it);

						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
			}
			monitor.done();
		}
	};
	
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
