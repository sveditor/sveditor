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

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBOpenDeclarationIncludeNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenDeclarationAction extends TextEditorAction {
	private SVEditor				fEditor;
	private LogHandle				fLog;
	private boolean					fDebugEn = true;

	public OpenDeclarationAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "OpenDeclaration.", editor);
		fLog = LogFactory.getLogHandle("OpenDeclarationAction");
		fEditor = editor;
		update();
	}

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

	@Override
	public void run() {
		debug("OpenDeclarationAction.run()");
		
		IDocument doc = fEditor.getDocumentProvider().getDocument(
				fEditor.getEditorInput());
		ITextSelection sel = getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();
		SVDBFile    		inc_file = null;
		SVDBItem			it = null;

		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		SVExpressionUtils		expr_utils = new SVExpressionUtils(new SVDBFindDefaultNameMatcher());
		
		SVExprContext expr_ctxt = expr_utils.extractExprContext(scanner, true);
		
		fLog.debug("Expression Context: root=" + expr_ctxt.fRoot +
				" trigger=" + expr_ctxt.fTrigger + " leaf=" + expr_ctxt.fLeaf);

		ISVDBIndexIterator index_it = fEditor.getIndexIterator();
		
		
		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();
		
		SVDBScopeItem active_scope = SVDBSearchUtils.findActiveScope(
				file, getTextSel().getStartLine());
		
		// If this is an include lookup, then use a different matching strategy
		if (expr_ctxt.fTrigger != null && expr_ctxt.fRoot != null &&
				expr_ctxt.fTrigger.equals("`") && expr_ctxt.fRoot.equals("include")) {
			expr_utils.setMatcher(new SVDBOpenDeclarationIncludeNameMatcher());
		}

		List<SVDBItem> items = expr_utils.findItems(index_it, active_scope, expr_ctxt, false);
		
		if (items.size() > 0) {
			it = items.get(0);
		}

		if (it != null) {
			SVEditorUtil.openEditor(it);
		} else if (inc_file != null) {
			SVEditorUtil.openEditor(inc_file.getFilePath());
		}
	}
	
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
