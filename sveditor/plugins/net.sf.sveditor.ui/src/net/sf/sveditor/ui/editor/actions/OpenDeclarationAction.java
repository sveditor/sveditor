/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenDeclarationAction extends TextEditorAction {
	private SVEditor				fEditor;
	private LogHandle				fLog;
	private boolean				fDebugEn = true;

	public OpenDeclarationAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "OpenDeclaration.", editor);
		fLog = LogFactory.getLogHandle("OpenDeclarationAction");
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

		Tuple<ISVDBItemBase, SVDBFile> target = findTarget();

		try {
			if (target.first() != null) {
				fLog.debug("Open file for item \"" + SVDBItem.getName(target.first())); 
				SVEditorUtil.openEditor(target.first());
			} else if (target.second() != null) {
				SVEditorUtil.openEditor(target.second().getFilePath());
			}
		} catch (PartInitException e) {
			fLog.error("Failed to open declaration in editor", e);
		}
	}
	
	protected SVDBFile getTargetFile() {
		return fEditor.getSVDBFile();
	}
	
	protected ISVDBIndexIterator getIndexIt() {
		return fEditor.getIndexIterator();
	}
	
	protected IDocument getDocument() {
		return fEditor.getDocumentProvider().getDocument(fEditor.getEditorInput());
	}
	
	protected Tuple<ISVDBItemBase, SVDBFile> findTarget() {
		IDocument doc = getDocument();
		ITextSelection sel = getTextSel();
		int offset = sel.getOffset() + sel.getLength();

		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		scanner.setSkipComments(true);
		
		List<Tuple<ISVDBItemBase, SVDBFile>> items = OpenDeclUtils.openDecl_2(
				getTargetFile(), 
				getTextSel().getStartLine(),
				scanner,
				getIndexIt());

		if (items.size() > 0) {
			return items.get(0);
		} else {
			return new Tuple<ISVDBItemBase, SVDBFile>(null, null);
		}
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
