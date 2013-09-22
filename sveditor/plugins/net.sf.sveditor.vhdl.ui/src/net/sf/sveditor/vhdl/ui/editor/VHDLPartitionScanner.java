package net.sf.sveditor.vhdl.ui.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

public class VHDLPartitionScanner extends RuleBasedPartitionScanner {
	
	public VHDLPartitionScanner() {
		super();
		
		IToken slc = new Token(VHDLDocumentPartitions.VHD_COMMENT);
		IToken str = new Token(VHDLDocumentPartitions.VHD_STRING);
		
		List<IPredicateRule> rules = new ArrayList<IPredicateRule>();
		
		rules.add(new EndOfLineRule("--", slc));
		rules.add(new SingleLineRule("\"", "\"", str, '\\'));
		
		setPredicateRules(rules.toArray(new IPredicateRule[rules.size()]));
	}

}
