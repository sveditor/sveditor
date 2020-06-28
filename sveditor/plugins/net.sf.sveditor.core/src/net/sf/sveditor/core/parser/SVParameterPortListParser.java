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


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBExpr;

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
		
		fLexer.readOperator(OP.HASH);
		fLexer.readOperator(OP.LPAREN);
		
		while (!fLexer.peekOperator(OP.RPAREN)) {
			String id = null;
			SVDBModIfcClassParam p;
			long it_start = fLexer.getStartLocation();
			boolean is_type = false;

			if (fLexer.peekKeyword(KW.PARAMETER, KW.LOCALPARAM)) {
				// TODO: need to preserve any of this?
				fLexer.eatToken();
			}

			// Parameter can be typed or untyped
			// type T=int
			// string Ts="foo"
			// parameter int c[1:0]
			if (fLexer.peekKeyword(KW.TYPE)) {
				fLexer.eatToken();
				id = fLexer.readIdOrKeyword();
				is_type = true;
			} else {
				// This might be a type
				SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);

				// If the next element is an operator, then the 
				// return from the type parser is the parameter name
				if (fLexer.peekOperator(OP.COMMA, OP.RPAREN, OP.EQ)) {
					id = type.getName();
				} else {
					// Otherwise, we have a type and a parameter name
					id = fLexer.readIdOrKeyword();
				}
			}
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				// TODO: handle vectored
				fLexer.skipPastMatch("[", "]");
			}
			
			// id now holds the template identifier
			p = new SVDBModIfcClassParam(id);
			p.setLocation(it_start);

			if (fLexer.peekOperator(OP.EQ)) {
				fLexer.eatToken();
				
				// TODO:
				// id = parsers().exprParser().expression().toString();
				// id = parsers().SVParser().readExpression(true);
				if (is_type) {
					SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
					p.setDefaultType(type);
				} else {
					SVDBExpr dflt = parsers().exprParser().expression();
					if (fDebugEn) {
						debug("parameter default: " + id);
					}
					p.setDefault(dflt);
				}
			}

			params.add(p);

			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(OP.RPAREN);
		
		
		return params;
	}

}
