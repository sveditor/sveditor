/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.argfile.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.svf_scanner.SVFScanner;
import net.sf.sveditor.ui.editor.CCommentRule;
import net.sf.sveditor.ui.editor.SLCommentRule;
import net.sf.sveditor.ui.editor.SVEditorColors;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

public class SVArgFileCodeScanner extends RuleBasedScanner {
	
	public SVArgFileCodeScanner() {
		updateRules();
	}
	
	public void updateRules() {
		IToken keyword = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.KEYWORD),
				null, SVEditorColors.getStyle(SVEditorColors.KEYWORD)));
		final IToken str = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING)));
		final IToken svt_param = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SVT_PARAMETERS),
				null, SVEditorColors.getStyle(SVEditorColors.SVT_PARAMETERS)));
		final IToken slc = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT)));
		final IToken mlc = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.MULTI_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.MULTI_LINE_COMMENT)));
		
		IToken default_t = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.DEFAULT),
				null, SVEditorColors.getStyle(SVEditorColors.DEFAULT)));

		setDefaultReturnToken(default_t);
		
		List<IRule> rules = new ArrayList<IRule>();

//		rules.add(new EndOfLineRule("//", slc));
		rules.add(new CCommentRule(mlc));
		rules.add(new SLCommentRule(slc));
//	    rules.add(new MultiLineRule("/*", "*/", mlc, (char) 0, true));"

	    rules.add(new SingleLineRule("\"", "\"", str, '\\'));
	    rules.add(new SingleLineRule("${", "}", svt_param));

		WordRule wordRule = new WordRule(new SVArgFileWordDetector(), default_t);
		
		// Argument File keywords
		for (String kw : SVFScanner.fRecognizedSwitches) {
			wordRule.addWord(kw, keyword);
		}
		
		rules.add(wordRule);

		// Add a coloring rule for pre-processor operations
		/*
		rules.add(new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				return SVCharacter.isSVIdentifierPart(c);
			}

			public boolean isWordStart(char c) {
				return (c == '`');
			}
		}, keyword));
		 */

		IRule[] ruleArray = rules.toArray(new IRule[rules.size()]);
		setRules(ruleArray);
	}
}
