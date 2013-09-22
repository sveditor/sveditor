package net.sf.sveditor.vhdl.ui.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.vhdl.parser.VHDLKeywords;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

public class VHDLCodeScanner extends RuleBasedScanner {
	
	public VHDLCodeScanner(VHDLEditor editor) {
		super();
		updateRules(editor);
	}
	
	public void updateRules(VHDLEditor editor) {
		final IToken keyword = new Token(new TextAttribute(
				editor.getColor(VHDLEditorColors.getColor(VHDLEditorColors.KEYWORD)),
				null, VHDLEditorColors.getStyle(VHDLEditorColors.KEYWORD)));
		final IToken str = new Token(new TextAttribute(
				editor.getColor(VHDLEditorColors.getColor(VHDLEditorColors.STRING)),
				null, VHDLEditorColors.getStyle(VHDLEditorColors.STRING)));
		final IToken slc = new Token(new TextAttribute(
				editor.getColor(VHDLEditorColors.getColor(VHDLEditorColors.COMMENT)),
				null, VHDLEditorColors.getStyle(VHDLEditorColors.COMMENT)));
		final IToken default_t = new Token(new TextAttribute(
				editor.getColor(VHDLEditorColors.getColor(VHDLEditorColors.DEFAULT)),
				null, VHDLEditorColors.getStyle(VHDLEditorColors.DEFAULT)));
				
		setDefaultReturnToken(default_t);
		List<IRule> rules = new ArrayList<IRule>();

		
		// rules.add(new EndOfLineRule("--", slc));
		
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
