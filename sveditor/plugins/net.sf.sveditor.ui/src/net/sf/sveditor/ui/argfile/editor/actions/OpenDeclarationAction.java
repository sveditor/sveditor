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


package net.sf.sveditor.ui.argfile.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.argfile.open_decl.SVArgFileOpenDeclaration;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.argfile.editor.SVArgFileEditor;
import net.sf.sveditor.ui.scanutils.SVArgFileDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenDeclarationAction extends TextEditorAction {
	private SVArgFileEditor			fEditor;
	private LogHandle				fLog;
	private boolean					fDebugEn = true;

	public OpenDeclarationAction(
			ResourceBundle			bundle,
			SVArgFileEditor			editor) {
		super(bundle, "ArgFileOpenFile.", editor);
		fLog = LogFactory.getLogHandle("ArgFileOpenFile");
		fEditor = editor;
		update();
	}
	
	protected ITextSelection getTextSel() {
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
		IDocument doc = getDocument();
		ITextSelection sel = getTextSel();
		int offset = sel.getOffset() + sel.getLength();
		SVArgFileDocumentTextScanner scanner = new SVArgFileDocumentTextScanner(doc, offset);
		
		scanner.setSkipComments(true);
		
		String path = SVArgFileOpenDeclaration.openDecl(scanner);
		
		if (path != null) {
			// Must use the context of this editor to resolve
			// the final path
			path = fEditor.resolvePath(path);

			try {
				SVEditorUtil.openEditor(path, null);
			} catch (PartInitException e) {
				// TODO: log failure
			}
		}
	}

	protected IDocument getDocument() {
		return fEditor.getDocumentProvider().getDocument(fEditor.getEditorInput());
	}

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
