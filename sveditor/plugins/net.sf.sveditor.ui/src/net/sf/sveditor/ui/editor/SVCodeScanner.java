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


package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.content.IContentType;
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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.ISVKeywords;
import net.sf.sveditor.core.parser.SVOperators;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVCodeScanner extends RuleBasedScanner {
	
	public SVCodeScanner(IContentType ct) {
		updateRules(ct);
	}
	
	public void updateRules(IContentType ct) {
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
		final IToken svt_params = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SVT_PARAMETERS),
				null, SVEditorColors.getStyle(SVEditorColors.SVT_PARAMETERS)));
		
		IToken default_t = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.DEFAULT),
				null, SVEditorColors.getStyle(SVEditorColors.DEFAULT)));

		setDefaultReturnToken(default_t);
		
		List<IRule> rules = new ArrayList<IRule>();
		
	    rules.add(new SingleLineRule("\"", "\"", str, '\\'));
		rules.add(new EndOfLineRule("//", slc));
	    rules.add(new MultiLineRule("/*", "*/", mlc, (char) 0, true));

	    rules.add(new SingleLineRule("${", "}", svt_params));
	    
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
		Set<ISVKeywords.KW> keywords = null;
		
		if (ct != null) {
			if (ct.getId().endsWith(".systemverilog") ) {
				keywords = ISVKeywords.KW.getSVKeywords();
			} else if (ct.getId().endsWith(".verilog")) {
				// Check if we are forcing all files to be treated as SV...
				// TODO: Should this apply to Verilog AMS too?
				if (SVCorePlugin.getDefault().getFileExtLanguageLevelOverride())  {
					keywords = ISVKeywords.KW.getSVKeywords();
				}
				else  {
					keywords = ISVKeywords.KW.getVLKeywords();
				}
			} else if (ct.getId().endsWith(".verilogams")) {
				keywords = ISVKeywords.KW.getAMSKeywords();
			}
		} 
		
		if (keywords == null) {
			keywords = ISVKeywords.KW.getSVKeywords();
		}
		
		for (ISVKeywords.KW kw : keywords) {
			String kw_s = kw.getImg();
			wordRule.addWord(kw_s, keyword);
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
		for (String op :SVOperators.AllOperators) {
			wordRule_ops.addWord(op, ops);
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
