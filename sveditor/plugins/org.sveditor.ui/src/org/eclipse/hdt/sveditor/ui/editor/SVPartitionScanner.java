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


package org.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

public class SVPartitionScanner extends RuleBasedPartitionScanner {
	
	public SVPartitionScanner() {
		super();
		
		IToken mlc = new Token(SVDocumentPartitions.SV_MULTILINE_COMMENT);
		IToken slc = new Token(SVDocumentPartitions.SV_SINGLELINE_COMMENT);
		/*
		IToken str = new Token(SVDocumentPartitions.SV_STRING);
		IToken svc = new Token(SVDocumentPartitions.SV_CODE);
		 */
		
		List<IPredicateRule> rules = new ArrayList<IPredicateRule>();
		
		rules.add(new CCommentRule(mlc));
		rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\'));
		rules.add(new EndOfLineRule("//", slc));
		
		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		setPredicateRules(rulesArr);
	}
}
