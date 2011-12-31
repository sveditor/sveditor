package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

public class NextWordAction extends TextEditorAction {
	private SVEditor				fEditor;
	
	public NextWordAction(
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
		} else {
			// scan forward to end or next identifier
			while (offset < len) {
				ch = str.charAt(offset);
				if (SVCharacter.isSVIdentifierPart(ch)) {
					break;
				}
				offset++;
			}
		}
		
		if (offset >= len) {
			offset = len-1;
		}
		
		text.setCaretOffset(offset);
	}
}
