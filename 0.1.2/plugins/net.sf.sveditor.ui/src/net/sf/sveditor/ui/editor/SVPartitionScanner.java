/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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
		rules.add(new EndOfLineRule("//", slc));
		rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\'));
		
		IPredicateRule rulesArr[] = rules.toArray(new IPredicateRule[rules.size()]);
		setPredicateRules(rulesArr);
	}
}
