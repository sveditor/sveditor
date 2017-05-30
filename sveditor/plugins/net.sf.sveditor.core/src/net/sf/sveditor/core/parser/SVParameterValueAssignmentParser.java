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

import java.util.List;

import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBNullExpr;

public class SVParameterValueAssignmentParser extends SVParserBase {
	
	public SVParameterValueAssignmentParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBParamValueAssignList parse(boolean is_parameter) throws SVParseException {
		SVDBParamValueAssignList ret = new SVDBParamValueAssignList();
		// StringBuilder v = new StringBuilder();

		if (is_parameter) {
			if (fLexer.peekOperator(OP.HASH)) {
				fLexer.eatToken();
			}
		}
		fLexer.readOperator(OP.LPAREN);
		while (fLexer.peek() != null && !fLexer.peekOperator(OP.RPAREN)) {
			boolean is_mapped = false;
			boolean is_wildcard = false;
			boolean is_implicit_connection = false;
			String name = null;
			if (!is_parameter && fLexer.peekOperator(OP.DOT_MUL)) {
				fLexer.eatToken();
				ret.addParameter(new SVDBParamValueAssign("*", (SVDBExpr)null));
				is_wildcard = true;
				is_mapped = true;
			} else if (fLexer.peekOperator(OP.DOT)) {
				fLexer.eatToken();
				name = fLexer.readId();
				// Check to see if the port has an ( as in ...
				// .portname (signal_connected),
				if (fLexer.peekOperator(OP.LPAREN))  {
					fLexer.readOperator(OP.LPAREN);
					is_mapped = true;
				}
				// Check to see if we have an implicit port connection, as in
				// .portname ,
				else if (fLexer.peekOperator(OP.COMMA))  {
					is_implicit_connection = true;
					is_mapped = true;
					// Grab name and put it into the DB as the same name as the port
					ret.addParameter(new SVDBParamValueAssign(name, (SVDBExpr)null));
				}
			}
			
			// Not an implicit connection or a wild card, we either have:
			// .portname ()
			// or
			// .portname (wirename)... handle both
			if (!is_wildcard && !is_implicit_connection) {
				// Allow an empty port-mapping entry: .foo()
				if (fLexer.peekOperator(OP.RPAREN)) {
					// Fill in a dummy name for the connection name
					// TODO: Check on the identifier type - guessing NullExpr
					ret.addParameter(new SVDBParamValueAssign(name, new SVDBNullExpr()));
				}
				else if (!fLexer.peekOperator(OP.RPAREN)) {
					List<SVToken> id_list = parsers().commonParserUtils().peekScopedStaticIdentifier_l(false);

					if (fLexer.peekOperator(OP.HASH) /*|| fLexer.peekKeyword(SVKeywords.fBuiltinTypes) ||
							fLexer.peekKeyword("virtual") */) {
						// This is actually a type reference
						fLexer.ungetToken(id_list);
						SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
						ret.addParameter(new SVDBParamValueAssign(name, type));
					}
					// Fix for: #453 Parser error: Unconnected ports being flagged as an error 
					// Could have the following code where ports are not named, and not connected
					// e.g. submodule sm (in1, in2, /*out1*/, out2);
					else if ((id_list.size() == 0) && !is_mapped && fLexer.peekOperator(OP.COMMA))  {
						// TODO: Matt: is this what we should be adding to the database?
						ret.addParameter("unconnected", null);
					}
					else {
						fLexer.ungetToken(id_list);
						SVDBExpr val = parsers().exprParser().datatype_or_expression();
						ret.addParameter(new SVDBParamValueAssign(name, val));
					}
				}

				if (is_mapped) {
					// Read inside
					fLexer.readOperator(OP.RPAREN);
				}

				//ret.addParameter(new SVDBParamValueAssign(name, v.toString()));
			}
			ret.setIsNamedMapping(is_mapped);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(OP.RPAREN);
		
		return ret;
	}
	
}
