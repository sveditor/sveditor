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


package org.eclipse.hdt.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBModIfcClassParam;

public class SVParameterDeclParser extends SVParserBase {
	// private SVExprParser				fExprParser;
	
	public SVParameterDeclParser(ISVParser parser) {
		super(parser);
		// fExprParser			= new SVExprParser(parser);
	}
	
	public List<SVDBModIfcClassParam> parse() throws SVParseException {
		List<SVDBModIfcClassParam> param_l = new ArrayList<SVDBModIfcClassParam>();
		fLexer.readOperator(OP.LPAREN);
		
		while (fLexer.peekKeyword(KW.TYPE) || fLexer.peekId()) {
			if (fLexer.peekKeyword(KW.TYPE)) {
				// TODO: recognize parameters as typed
				fLexer.eatToken();
			}
			// SVDBModIfcClassParam p = new SVDBModIfcClassParam(fLexer.getImage());
			
			// TODO: {unpacked dimension}
			
			fLexer.readOperator(OP.EQ);
			
			
		}
		
		return param_l;
	}
}
