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


package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

public class SVDocumentSetupParticipant implements IDocumentSetupParticipant {

	public void setup(IDocument doc) {
		if (doc instanceof IDocumentExtension3) {
			IDocumentExtension3 docExt = (IDocumentExtension3)doc;
			IDocumentPartitioner p = createPartitioner();
			docExt.setDocumentPartitioner(SVDocumentPartitions.SV_PARTITIONING, p);
			p.connect(doc);
		}
	}
	
	public static IDocumentPartitioner createPartitioner() {
		IDocumentPartitioner p = new FastPartitioner(
				createScanner(), SVDocumentPartitions.SV_PARTITION_TYPES);

		return p;
	}
	
	private static IPartitionTokenScanner createScanner() {
		RuleBasedPartitionScanner scanner = new RuleBasedPartitionScanner();

		
		IToken mlc = new Token(SVDocumentPartitions.SV_MULTILINE_COMMENT);
		IToken slc = new Token(SVDocumentPartitions.SV_SINGLELINE_COMMENT);
		
		List<IPredicateRule> rules = new ArrayList<IPredicateRule>();
		
		rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\'));
		rules.add(new EndOfLineRule("//", slc));
		rules.add(new CCommentRule(mlc));

		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		scanner.setDefaultReturnToken(new Token(IDocument.DEFAULT_CONTENT_TYPE));
		scanner.setPredicateRules(rulesArr);

		return scanner;
	}
}
