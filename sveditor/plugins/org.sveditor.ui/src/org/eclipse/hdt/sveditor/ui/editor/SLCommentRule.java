/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.ui.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

public class SLCommentRule implements IPredicateRule {
	private IToken			fToken;
	
	public SLCommentRule(IToken tok) {
		fToken = tok;
	}

	public IToken evaluate(ICharacterScanner scanner, boolean resume) {
		boolean in_comment = resume;
		
		if (!resume) {
			if (scanner.read() == '/') {
				if (scanner.read() == '/') {
					in_comment = true;
				} else {
					scanner.unread();
					scanner.unread();
				}
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
		
		int ch; // , last_ch=-1;
		while ((ch = scanner.read()) != ICharacterScanner.EOF) {
			if (ch == '\n' || ch == '\r') {
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
