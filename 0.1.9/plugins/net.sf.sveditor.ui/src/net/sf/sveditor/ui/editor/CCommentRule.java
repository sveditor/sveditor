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

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

public class CCommentRule implements IPredicateRule {
	private IToken			fToken;
	
	public CCommentRule(IToken tok) {
		fToken = tok;
	}

	public IToken evaluate(ICharacterScanner scanner, boolean resume) {
		boolean in_comment = resume;
		
		if (!resume) {
			if (scanner.read() == '/') {
				if (scanner.read() == '*') {
					in_comment = true;
				}
				scanner.unread();
			} else {
				scanner.unread();
			}
		}
		
		if (in_comment) {
			scanToEnd(scanner);
			return fToken;
		}
		
		return Token.UNDEFINED;
	}
	
	private void scanToEnd(ICharacterScanner scanner) {
		int ch_a[] = {-1, -1};
		
		int ch;
		while ((ch = scanner.read()) != ICharacterScanner.EOF) {
			ch_a[0] = ch_a[1];
			ch_a[1] = ch;
			
			if (ch_a[0] == '*' && ch_a[1] == '/') {
				break;
			}
		}
	}
	
	public IToken evaluate(ICharacterScanner scanner) {
		return evaluate(scanner, false);
	}

	public IToken getSuccessToken() {
		return fToken;
	}


}
