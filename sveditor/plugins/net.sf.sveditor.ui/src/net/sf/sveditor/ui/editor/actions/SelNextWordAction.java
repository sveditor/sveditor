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
		StyledText text = fEditor.sourceViewer().getTextWidget();
		int offset = text.getCaretOffset();
		int start_offset = offset;
		
		// Adjust start_offset if selection currently set
		if (text.getSelection() != null) {
			Point sel = text.getSelection();
			if (sel.x == offset) {
				// contracting
				start_offset = sel.y;
			} else if (sel.y == offset) {
				// extending
				start_offset = sel.x;
			}
		}
		
		String str = text.getText();
		int len = str.length();
		
		int ch = str.charAt(offset);
		if (SVCharacter.isSVIdentifierPart(ch)) {
			// scan forward to end or next non-id_part
			while (offset < len) {
				ch = str.charAt(offset);
				if (!SVCharacter.isSVIdentifierPart(ch)) {
					break;
				}
				offset++;
			}
		} else if (Character.isWhitespace(ch)) {
			// scan forward through whitespace
			while (offset < len) {
				ch = str.charAt(offset);
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
		
		if (offset >= len) {
			offset = len-1;
		}
		
		// Move cursor to end position
		text.setCaretOffset(offset);
		// Set selection bounds
		text.setSelection(start_offset, offset);
	}
}
