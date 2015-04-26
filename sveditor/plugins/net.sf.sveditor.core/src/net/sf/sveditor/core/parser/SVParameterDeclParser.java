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


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;

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
