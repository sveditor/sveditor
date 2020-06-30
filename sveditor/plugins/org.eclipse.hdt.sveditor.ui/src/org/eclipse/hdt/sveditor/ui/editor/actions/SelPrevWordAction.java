/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.ui.editor.SVEditor;

import org.eclipse.hdt.sveditor.core.scanner.SVCharacter;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.texteditor.TextEditorAction;

public class SelPrevWordAction extends TextEditorAction {
	private SVEditor				fEditor;
	
	public SelPrevWordAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fEditor = editor;
	}

	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		StyledText text = fEditor.sourceViewer().getTextWidget();
		IDocument doc = sv.getDocument();
		ITextSelection tsel = (ITextSelection)fEditor.getSite().getSelectionProvider().getSelection();
		int offset = text.getCaretOffset();
		int start_offset = offset;
		
		// Adjust start_offset if selection currently set
		// In this case, we're tracking the outer bound of the selection
		if (text.getSelection() != null) {
			Point sel = text.getSelection();
			// If the caret is placed at the base of the region, extend.
			// If the caret is placed at the limit, contract
			// Otherwise, just reset
			if (sel.x == offset) {
				start_offset = (tsel.getOffset()+tsel.getLength());
				offset = tsel.getOffset();
			} else if (sel.y == offset) {
				start_offset = tsel.getOffset();
				offset = (tsel.getOffset()+tsel.getLength());
			}
		}
		
		offset--;
		if (offset < 0) {
			return;
		}
	
		try {
			int ch = doc.getChar(offset);
			if (SVCharacter.isSVIdentifierPart(ch)) {
				// scan back to end or next non-id_part
				while (offset >= 0) {
					ch = doc.getChar(offset);
					if (!SVCharacter.isSVIdentifierPart(ch)) {
						break;
					}
					offset--;
				}
			} else if (Character.isWhitespace(ch)) {
				// scan back to end or end of whitespace
				while (offset >= 0) {
					ch = doc.getChar(offset);
					if (!Character.isWhitespace(ch)) {
						break;
					}
					offset--;
				}
			} else {
				offset--;
			}
		} catch (BadLocationException e) {}
		
		if (offset < 0) {
			offset = 0;
		}
		offset++;
	
		sv.setSelectedRange(start_offset, offset-start_offset);
	}
}
