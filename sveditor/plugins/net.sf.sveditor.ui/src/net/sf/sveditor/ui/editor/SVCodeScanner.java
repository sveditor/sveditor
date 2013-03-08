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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

public class SVCodeScanner extends RuleBasedScanner {
	
	public SVCodeScanner() {
		updateRules();
	}
	
	public void updateRules() {
		IToken keyword = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.KEYWORD),
				null, SVEditorColors.getStyle(SVEditorColors.KEYWORD)));
		final IToken str = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING)));
		final IToken slc = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT)));
		final IToken mlc = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.MULTI_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.MULTI_LINE_COMMENT)));
		final IToken brace = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.BRACE),
				null, SVEditorColors.getStyle(SVEditorColors.BRACE)));
		final IToken nums = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.NUMBERS),
				null, SVEditorColors.getStyle(SVEditorColors.NUMBERS)));
		final IToken ops = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.OPERATORS),
				null, SVEditorColors.getStyle(SVEditorColors.OPERATORS)));
		
		IToken default_t = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.DEFAULT),
				null, SVEditorColors.getStyle(SVEditorColors.DEFAULT)));

		setDefaultReturnToken(default_t);
		
		List<IRule> rules = new ArrayList<IRule>();
		
		rules.add(new EndOfLineRule("//", slc));
	    rules.add(new MultiLineRule("/*", "*/", mlc, (char) 0, true));

	    rules.add(new SingleLineRule("\"", "\"", str, '\\'));
/*
		rules.add(new IRule() {
			public IToken evaluate(ICharacterScanner scanner) {
				int startCh = scanner.read();
				int ch;
				int unreadCount = 1;
				
				if (startCh == '"') {
					do {
						ch = scanner.read();
					} while (Character.isDefined((char)ch) && ch != '"');
					
					return str;
				}
				
				do {
					scanner.unread();
				} while (--unreadCount > 0);
				return Token.UNDEFINED;
			}
		});
 */

		WordRule wordRule = new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				return SVCharacter.isSVIdentifierPart(c);
			}
			
			public boolean isWordStart(char c) {
				return SVCharacter.isSVIdentifierStart(c);
			}
		}, default_t);
		
		
		// SV Keywords
		for (String kw :SVKeywords.getKeywords()) {
			String kw_p = kw;
			if (kw.endsWith("*")) {
				kw_p = kw.substring(0, kw.length()-1);
			}
			wordRule.addWord(kw_p, keyword);
		}
		// SV System Calls
		for (String kw :SVKeywords.getSystemCalls()) {
			String kw_p = kw;
			if (kw.endsWith("*")) {
				kw_p = kw.substring(0, kw.length()-1);
			}
			wordRule.addWord(kw_p, keyword);
		}
		
		rules.add(wordRule);

		// Add a coloring rule for braces
		rules.add(new WordRule(new IWordDetector() {

			public boolean isWordPart(char c) {
				return false;
			}
			
			public boolean isWordStart(char c) {
				final char fBraceStrings[] = {
						'[',
						']',
						'(',
						')',
						'{',
						'}'
				};
				for (char ch : fBraceStrings)  {
					if (ch == c)
						return true;
				}
				return false;
			}
		}, brace));
		

		// Add a coloring rule for pre-processor operations
		rules.add(new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				return SVCharacter.isSVIdentifierPart(c);
			}

			public boolean isWordStart(char c) {
				return (c == '`');
			}
		}, keyword));

		// Operators
		WordRule wordRule_ops = new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				for (char ch : "+-*/^%|&~!=<>?".toCharArray())  {
					if (ch == c)
						return true;
				}
				return false;
			}
			
			public boolean isWordStart(char c) {
				for (char ch : "+-*/^%|&~!=<>?:".toCharArray())  {
					if (ch == c)
						return true;
				}
				return false;
			}
		}, default_t);

		// Operators
		for (String kw :SVKeywords.fAssignmentOps) {
			wordRule_ops.addWord(kw, ops);
		}
		for (String kw :SVKeywords.fBinaryOps) {
			wordRule_ops.addWord(kw, ops);
		}

		rules.add (wordRule_ops);
		
		// Add a coloring rule for numbers
		// This is last in the hierarchy because this something of a "if all else fails" type rule
		rules.add(new WordRule(new IWordDetector() {
			
			public boolean isWordPart(char c) {
				final char fBraceStrings[] = "0123456789'hdbo_abcdefABCDEFzxZX?".toCharArray();
				for (char ch : fBraceStrings)  {
					if (ch == c)
						return true;
				}
				return false;
			}
			
			public boolean isWordStart(char c) {
				final char fBraceStrings[] = "0123456789'".toCharArray();
				for (char ch : fBraceStrings)  {
					if (ch == c)
						return true;
				}
				return false;
			}
		}, nums));
		
		
		IRule[] ruleArray = rules.toArray(new IRule[rules.size()]);
		setRules(ruleArray);
	}
}
