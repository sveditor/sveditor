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
		
		rules.add(new CCommentRule(mlc));
		rules.add(new EndOfLineRule("//", slc));
		rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\'));
		
		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		setPredicateRules(rulesArr);
	}
}
