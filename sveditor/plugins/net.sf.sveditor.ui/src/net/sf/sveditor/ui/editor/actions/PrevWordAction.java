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


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

public class PrevWordAction extends TextEditorAction {
	private SVEditor				fEditor;
	
	public PrevWordAction(
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
		
		String str = text.getText();
		
		offset--;
		if (offset < 0) {
			return;
		}
		
		
		int ch = str.charAt(offset);
		if (SVCharacter.isSVIdentifierPart(ch)) {
			// scan back to end or next non-id_part
			while (offset >= 0) {
				ch = str.charAt(offset);
				if (!SVCharacter.isSVIdentifierPart(ch)) {
					break;
				}
				offset--;
			}
		} else {
			// scan back to end or next identifier
			while (offset >= 0) {
				ch = str.charAt(offset);
				if (SVCharacter.isSVIdentifierPart(ch)) {
					break;
				}
				offset--;
			}
		}
		
		if (offset < 0) {
			offset = 0;
		}
		text.setCaretOffset(++offset);
	}
}
