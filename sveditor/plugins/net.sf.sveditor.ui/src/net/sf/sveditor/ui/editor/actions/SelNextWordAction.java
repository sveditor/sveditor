/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.texteditor.TextEditorAction;

public class SelNextWordAction extends TextEditorAction {
	private SVEditor				fEditor;
	
	public SelNextWordAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fEditor = editor;
	}

	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		IDocument doc = sv.getDocument();
		ITextSelection tsel = (ITextSelection)fEditor.getSite().getSelectionProvider().getSelection();
		
		StyledText text = fEditor.sourceViewer().getTextWidget();
		int offset = text.getCaretOffset();
		int start_offset = offset;
		
		// Adjust start_offset if selection currently set
		if (text.getSelection() != null) {
			Point sel = text.getSelection();
			
			if (sel.x == offset) {
				// Caret on the LHS of selection.
				// Selection is contracting
				offset = tsel.getOffset();
				start_offset = (tsel.getOffset()+tsel.getLength());
			} else if (sel.y == offset) {
				// Caret on RHS of selection
				// Selection is extending
				offset = tsel.getOffset()+tsel.getLength();
				start_offset = tsel.getOffset();
			}
		}
		
		int len = doc.getLength();
		try {
			int ch = doc.getChar(offset);
			if (SVCharacter.isSVIdentifierPart(ch)) {
				// scan forward to end or next non-id_part
				while (offset < len) {
					ch = doc.getChar(offset);
					if (!SVCharacter.isSVIdentifierPart(ch)) {
						break;
					}
					offset++;
				}
			} else if (Character.isWhitespace(ch)) {
				// scan forward through whitespace
				while (offset < len) {
					ch = doc.getChar(offset);
					if (!Character.isWhitespace(ch)) {
						break;
					}
					offset++;
				}
			} else {
				// Not identifier and not whitespace. Skip forward one.
				if (offset+1 < len) {
					offset++;
				}
			}
		} catch (BadLocationException e) {}
		
		if (offset >= len) {
			offset = len-1;
		}
		
		sv.setSelectedRange(start_offset, offset-start_offset);
		/*
		if (offset < start_offset) {
			sv.setSelectedRange(offset, 0);
			sv.setSelectedRange(offset, (start_offset-offset));
		} else {
			sv.setSelectedRange(start_offset, Math.abs(offset-start_offset));
		}
		 */
	}
}
