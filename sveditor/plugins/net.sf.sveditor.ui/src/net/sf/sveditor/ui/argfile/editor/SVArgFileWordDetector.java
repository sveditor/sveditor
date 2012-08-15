package net.sf.sveditor.ui.argfile.editor;

import org.eclipse.jface.text.rules.IWordDetector;

public class SVArgFileWordDetector implements IWordDetector {
	private boolean				fStartsWithPlus;
	private char				fLastCh = ' ';

	@Override
	public boolean isWordStart(char c) {
		fStartsWithPlus = (c == '+');
		fLastCh = ' ';
		return (Character.isJavaIdentifierStart(c) || c == '+' || c == '-');
	}

	@Override
	public boolean isWordPart(char c) {
		if (fLastCh == '+' && fStartsWithPlus) {
			return false;
		} else {
			fLastCh = c;
			return (Character.isJavaIdentifierPart(c) || c == '+');
		}
	}

}
