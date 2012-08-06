/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed for use in SVEditor
 *******************************************************************************/
package net.sf.sveditor.ui.editor.actions ;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindNamedPackage;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;


public class SelectionConverter {


	private SelectionConverter() {
		// no instance
	}
	
	public static ISVDBItemBase getElementAtOffset(SVEditor editor) {
		ITextSelection sel = null ;
		
		ISelection sel_o = editor.getSelectionProvider().getSelection();
		if (sel_o != null && sel_o instanceof ITextSelection) {
			sel = (ITextSelection)sel_o;
		} 		
		
		if(sel==null) {
		   return null ;
		}
			
		int offset = sel.getOffset() + sel.getLength();
		
		return getElementAt(editor, offset);
				
	}

	public static ISVDBItemBase getElementAt(SVEditor editor, int offset) {
		
		IDocument doc = editor.getDocumentProvider().getDocument(
				editor.getEditorInput());
		
		SVDocumentTextScanner scanner = new SVDocumentTextScanner(doc, offset) ;
		
		SVExprScanner			expr_scanner = new SVExprScanner();
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
		

		if (expr_ctxt.fLeaf != null && 
				(expr_ctxt.fTrigger == null || 
				 expr_ctxt.fTrigger.equals(""))) {
			
			List<ISVDBChildItem> found ;
			
			// FIXME: currently only looks for class/module/if and package declarations
			// as it is only the quick hierarchy and package/class diagram using this.
			
			SVDBFindNamedPackage findNamedPkg = new SVDBFindNamedPackage(editor.getIndexIterator()) ;
			
			found = findNamedPkg.find(expr_ctxt.fLeaf); 
			ISVDBItemBase pkg = (found != null && found.size() > 0) ? found.get(0) : null ; 
			
			if(pkg != null) {
				return pkg ;
			}
			
			SVDBFindNamedModIfcClassIfc finder_c = new SVDBFindNamedModIfcClassIfc(
					editor.getIndexIterator()) ;
			
				found = finder_c.find(expr_ctxt.fLeaf); 
				ISVDBItemBase cls = (found != null && found.size() > 0)?found.get(0):null; 
				
				if(cls == null) {
					return null ;
				} else {
					return cls ;
				}

		}
		
		return null ;
	}



}

