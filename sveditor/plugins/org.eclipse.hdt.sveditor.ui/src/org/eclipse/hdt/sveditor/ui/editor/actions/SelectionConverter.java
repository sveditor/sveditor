/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed for use in SVEditor
 *******************************************************************************/
package org.eclipse.hdt.sveditor.ui.editor.actions ;

import java.util.List;

import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedPackage;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprContext;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprScanner;
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
			
			// FIXME: currently only looks for class/module/if and package declarations
			// as it is only the quick hierarchy and package/class diagram using this.
			
			SVDBFindNamedPackage findNamedPkg = new SVDBFindNamedPackage(editor.getIndexIterator()) ;
			
			List<SVDBDeclCacheItem> found_p = findNamedPkg.find(expr_ctxt.fLeaf); 
			ISVDBItemBase pkg = null;
			if (found_p != null && found_p.size() > 0) {
				pkg = found_p.get(0).getSVDBItem();
			}
			
			if(pkg != null) {
				return pkg ;
			}
			
			SVDBFindNamedModIfcClassIfc finder_c = new SVDBFindNamedModIfcClassIfc(
					editor.getIndexIterator()) ;
			
				List<SVDBDeclCacheItem> found_c = finder_c.findItems(expr_ctxt.fLeaf); 
				ISVDBItemBase cls = null;
				if (found_c != null && found_c.size() > 0) {
					cls = found_c.get(0).getSVDBItem();
				}
				
				if(cls == null) {
					return null ;
				} else {
					return cls ;
				}
		}
		
		return null ;
	}



}

