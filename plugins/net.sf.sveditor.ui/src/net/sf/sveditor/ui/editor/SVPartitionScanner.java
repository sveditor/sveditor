package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

public class SVPartitionScanner extends RuleBasedPartitionScanner {
	
	public SVPartitionScanner() {
		super();
		
		IToken mlc = new Token(SVDocumentPartitions.SV_MULTILINE_COMMENT);
		IToken slc = new Token(SVDocumentPartitions.SV_SINGLELINE_COMMENT);
		IToken str = new Token(SVDocumentPartitions.SV_STRING);
		IToken svc = new Token(SVDocumentPartitions.SV_CODE);
		
		List<IPredicateRule> rules = new ArrayList<IPredicateRule>();
		
		rules.add(new MultiLineRule("/*", "*/", mlc, (char)0, true));
		rules.add(new EndOfLineRule("//", Token.UNDEFINED));
		rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\'));
		
		// handle empty comments
		// rules.add(new EmptyCommentPredicateRule(mlc));


		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		setPredicateRules(rulesArr);
	}

	private static class EmptyCommentDetector implements IWordDetector {
		public boolean isWordStart(char c) {
			return (c == '/');
		}
		
		public boolean isWordPart(char c) {
			return ((c == '*') || (c == '/'));
		}
	}
	
	private static class EmptyCommentPredicateRule extends WordRule implements IPredicateRule {
		
		private IToken			fSuccessToken;
		
		public EmptyCommentPredicateRule(IToken successToken) {
			super(new EmptyCommentDetector());
			fSuccessToken = successToken;
			addWord("/**/", fSuccessToken);
		}
		
		public IToken evaluate(ICharacterScanner scanner, boolean resume) {
			return super.evaluate(scanner);
		}
		
		public IToken getSuccessToken() {
			return fSuccessToken;
		}
	}
	
}
