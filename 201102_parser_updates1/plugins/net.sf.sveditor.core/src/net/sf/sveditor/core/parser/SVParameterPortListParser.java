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


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVParameterPortListParser extends SVParserBase {
	
	public SVParameterPortListParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * parameter_port_list ::=
	 * 	# ( list_of_param_assignments { , parameter_port_declaration } )
	 * 	| # ( parameter_port_declaration { , parameter_port_declaration } )
	 * 	| #( )
	 * 
	 * @return
	 * @throws SVParseException
	 */
	public List<SVDBModIfcClassParam> parse() throws SVParseException {
		List<SVDBModIfcClassParam> params = new ArrayList<SVDBModIfcClassParam>();
		
		fLexer.readOperator("#");
		fLexer.readOperator("(");
		
		while (!fLexer.peekOperator(")")) {
			String id = null;
			SVDBModIfcClassParam p;
			SVDBLocation it_start = fLexer.getStartLocation();
			boolean is_type = false;

			// Parameter can be typed or untyped
			// type T=int
			// string Ts="foo"
			// parameter int c[1:0]
			if (fLexer.peekKeyword("type")) {
				fLexer.eatToken();
				id = fLexer.readIdOrKeyword();
				is_type = true;
			} else {
				if (fLexer.peekKeyword("parameter")) {
					fLexer.eatToken();
				}
				// This might be a type
				SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
				
				// If the next element is an operator, then the 
				// return from the type parser is the parameter name
				if (fLexer.peekOperator(",", ")", "=")) {
					id = type.getName();
				} else {
					// Otherwise, we have a type and a parameter name
					id = fLexer.readIdOrKeyword();
				}
			}
			
			if (fLexer.peekOperator("[")) {
				// TODO: handle vectored
				fLexer.skipPastMatch("[", "]");
			}
			
			// id now holds the template identifier
			p = new SVDBModIfcClassParam(id);
			p.setLocation(it_start);

			if (fLexer.peekOperator("=")) {
				fLexer.eatToken();
				
				// TODO:
				// id = parsers().exprParser().expression().toString();
				// id = parsers().SVParser().readExpression(true);
				if (is_type) {
					SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
					p.setDefaultType(type);
				} else {
					SVExpr dflt = parsers().exprParser().expression();
					debug("parameter default: " + id);
					p.setDefault(dflt);
				}
			}

			params.add(p);

			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(")");
		
		
		return params;
	}

}
