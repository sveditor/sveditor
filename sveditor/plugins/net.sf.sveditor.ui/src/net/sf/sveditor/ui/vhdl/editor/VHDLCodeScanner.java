package net.sf.sveditor.ui.vhdl.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.vhdl.parser.VHDLKeywords;
import net.sf.sveditor.ui.editor.SVEditorColors;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

public class VHDLCodeScanner extends RuleBasedScanner {
	
	public VHDLCodeScanner(VHDLEditor editor) {
		super();
		updateRules(editor);
	}
	
	public void updateRules(VHDLEditor editor) {
//		VhdlLexer lexer = new VhdlLexer(new StringInputStream(""));
		final IToken keyword = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.KEYWORD),
				null, SVEditorColors.getStyle(SVEditorColors.KEYWORD)));
		final IToken str = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING)));
		final IToken slc = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT)));
		final IToken default_t = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.DEFAULT),
				null, SVEditorColors.getStyle(SVEditorColors.DEFAULT)));
		final IToken svt_params = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SVT_PARAMETERS),
				null, SVEditorColors.getStyle(SVEditorColors.SVT_PARAMETERS)));
				
		setDefaultReturnToken(default_t);
		List<IRule> rules = new ArrayList<IRule>();
		
		rules.add(new EndOfLineRule("--",  slc));
		rules.add(new SingleLineRule("\"", "\"", str, '\\'));
	    rules.add(new SingleLineRule("${", "}", svt_params));

		WordRule word_rule = new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				return Character.isJavaIdentifierPart(c);
			}
			public boolean isWordStart(char c) {
				return Character.isJavaIdentifierStart(c);
			}
		}, default_t, true);

		for (String kw : VHDLKeywords.getKeywords()) {
			word_rule.addWord(kw, keyword);
		}
		rules.add(word_rule);

		WhitespaceRule ws = new WhitespaceRule(new IWhitespaceDetector() {
			
			public boolean isWhitespace(char c) {
				return Character.isWhitespace(c);
			}
		});
		rules.add(ws);

		setRules(rules.toArray(new IRule[rules.size()]));
	}

}
