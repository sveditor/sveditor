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


package net.sf.sveditor.ui.editor;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;

public class SVEditorTextHover implements ITextHover /*, ITextHoverExtension */ {
	private SVEditor					fEditor;
	// private boolean						fHoverEnabled;
	
	public SVEditorTextHover(SVEditor editor, ITextViewer viewer) {
		fEditor = editor;
	}

	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		SVDocumentTextScanner scanner = 
			new SVDocumentTextScanner(textViewer.getDocument(), hoverRegion.getOffset()+1);
		SVExpressionUtils expr_utils = new SVExpressionUtils(new SVDBFindDefaultNameMatcher());
		SVExprScanner expr_scanner = new SVExprScanner();
		
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
		
		int lineno = -1;
		try {
			lineno = textViewer.getDocument().getLineOfOffset(hoverRegion.getOffset()); 
		} catch (BadLocationException e) { }
		
		ISVDBScopeItem src_scope = null;
		
		if (lineno != -1) {
			src_scope = SVDBSearchUtils.findActiveScope(fEditor.getSVDBFile(), lineno);
		}
		
		String str = null;
		if (src_scope != null) {
			/*
			List<SVDBItem> info = expr_utils.processPreTriggerPortion(
					fEditor.getIndexIterator(), src_scope, expr_ctxt.fRoot, true);
			 */
			List<ISVDBItemBase> info = expr_utils.findItems(
					fEditor.getIndexIterator(), src_scope, expr_ctxt, false);
			
			if (info != null && info.size() > 0) {
				ISVDBItemBase it = info.get(0);
				str = it.getType() + " : ";
				if (it instanceof ISVDBNamedItem) {
					str += ((ISVDBNamedItem)it).getName();
				}
			}
		}
		
		return str;
	}

	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		return findWord(textViewer.getDocument(), offset);
	}
	
	public IInformationControlCreator getHoverControlCreator() {
		// TODO Auto-generated method stub
		return null;
	}

	private IRegion findWord(IDocument document, int offset) {
		int start= -2;
		int end= -1;

		try {

			int pos= offset;
			char c;

			while (pos >= 0) {
				c= document.getChar(pos);
				if (!Character.isUnicodeIdentifierPart(c))
					break;
				--pos;
			}

			start= pos;

			pos= offset;
			int length= document.getLength();

			while (pos < length) {
				c= document.getChar(pos);
				if (!Character.isUnicodeIdentifierPart(c))
					break;
				++pos;
			}

			end= pos;

		} catch (BadLocationException x) {
		}

		if (start >= -1 && end > -1) {
			if (start == offset && end == offset)
				return new Region(offset, 0);
			else if (start == offset)
				return new Region(start, end - start);
			else
				return new Region(start + 1, end - start - 1);
		}

		return null;
	}

}
