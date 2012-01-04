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

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.core.hierarchy.ModuleHierarchyTreeFactory;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;
import net.sf.sveditor.ui.views.hierarchy.SVHierarchyView;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

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
				SVDBFindNamedModIfcClassIfc finder_c = new SVDBFindNamedModIfcClassIfc(
						((SVEditor)getTextEditor()).getIndexIterator());
				
				List<ISVDBChildItem> result = finder_c.find(expr_ctxt.fLeaf); 
				ISVDBItemBase cls = (result != null && result.size() > 0)?result.get(0):null; 

				monitor.worked(1);

				if (cls != null) {
					HierarchyTreeNode n = null;
					if (cls.getType() == SVDBItemType.ClassDecl) {
						ClassHierarchyTreeFactory factory = new ClassHierarchyTreeFactory(
								((SVEditor)getTextEditor()).getIndexIterator());

						n = factory.build((SVDBClassDecl)cls);
					} else if (cls.getType() == SVDBItemType.ModuleDecl) {
						ModuleHierarchyTreeFactory factory = new ModuleHierarchyTreeFactory(
								((SVEditor)getTextEditor()).getIndexIterator());
						
						n = factory.build((SVDBModIfcDecl)cls);
					}

					monitor.worked(1);
					
					if (n != null) {
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
