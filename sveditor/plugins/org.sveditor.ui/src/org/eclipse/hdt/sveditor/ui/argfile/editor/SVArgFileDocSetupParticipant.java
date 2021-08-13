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


package org.sveditor.ui.argfile.editor;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.ui.editor.CCommentRule;
import org.sveditor.ui.editor.SLCommentRule;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

public class SVArgFileDocSetupParticipant implements IDocumentSetupParticipant {

	public void setup(IDocument doc) {
		if (doc instanceof IDocumentExtension3) {
			IDocumentExtension3 docExt = (IDocumentExtension3)doc;
			IDocumentPartitioner p = createPartitioner();
			docExt.setDocumentPartitioner(SVArgFileDocumentPartitions.SV_ARGFILE_PARTITIONING, p);
			p.connect(doc);
		}
	}
	
	public static IDocumentPartitioner createPartitioner() {
		IDocumentPartitioner p = new FastPartitioner(
				createScanner(), SVArgFileDocumentPartitions.SV_ARGFILE_PARTITION_TYPES);

		return p;
	}
	
	private static IPartitionTokenScanner createScanner() {
		RuleBasedPartitionScanner scanner = new RuleBasedPartitionScanner();

		
		IToken mlc = new Token(SVArgFileDocumentPartitions.SV_ARGFILE_MULTILINE_COMMENT);
		IToken slc = new Token(SVArgFileDocumentPartitions.SV_ARGFILE_SINGLELINE_COMMENT);
		
		List<IPredicateRule> rules = new ArrayList<IPredicateRule>();
		
//		rules.add(new EndOfLineRule("//", slc));
		rules.add(new CCommentRule(mlc));
		rules.add(new SLCommentRule(slc));

		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		scanner.setDefaultReturnToken(new Token(IDocument.DEFAULT_CONTENT_TYPE));
		scanner.setPredicateRules(rulesArr);

		return scanner;
	}
}

