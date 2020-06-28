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

import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoBuiltin;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDimItem;

public class SVTaskFunctionPortListParser extends SVParserBase {
	
	public SVTaskFunctionPortListParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBParamPortDecl> parse() throws SVParseException {
		List<SVDBParamPortDecl> params = new ArrayList<SVDBParamPortDecl>();
		int dir = SVDBParamPortDecl.Direction_Input;
		SVDBTypeInfo last_type = null;
		
		fLexer.readOperator(OP.LPAREN);
		
		// Empty parameter list
		if (fLexer.peekOperator(OP.RPAREN)) {
			fLexer.eatToken();
			return params;
		}
		
		while (true) {
			long it_start = fLexer.getStartLocation();
			if (fLexer.peekKeyword(KW.INPUT, KW.OUTPUT, KW.INOUT, KW.REF)) {
				String dir_s = fLexer.eatTokenR();
				if (dir_s.equals("input")) {
					dir = SVDBParamPortDecl.Direction_Input;
				} else if (dir_s.equals("output")) {
					dir = SVDBParamPortDecl.Direction_Output;
				} else if (dir_s.equals("inout")) {
					dir = SVDBParamPortDecl.Direction_Inout;
				} else if (dir_s.equals("ref")) {
					dir = SVDBParamPortDecl.Direction_Ref;
				}
			} else if (fLexer.peekKeyword(KW.CONST)) {
				fLexer.eatToken();
				fLexer.readKeyword(KW.REF);
				dir = (SVDBParamPortDecl.Direction_Ref | SVDBParamPortDecl.Direction_Const);
			}
			
			if (fLexer.peekKeyword(KW.VAR)) {
				fLexer.eatToken();
				dir |= SVDBParamPortDecl.Direction_Var;
			}
			
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);

			// This could be a continuation of the same type: int a, b, c
			if (fLexer.peekOperator(OP.LBRACKET)) {
				List<SVDBVarDimItem> dim = fParsers.dataTypeParser().vector_dim();
				if (type instanceof SVDBTypeInfoBuiltin) {
					((SVDBTypeInfoBuiltin)type).setVectorDim(dim);
				} else {
					// TODO:
				}
			}

			String id;

			// Handle the case where a single type and a 
			// list of parameters is declared
			if (fLexer.peekOperator(OP.COMMA, OP.RPAREN, OP.EQ, OP.LBRACKET)) {
				// use previous type
				id = type.getName();
				type = last_type;
			} else {

				id = fLexer.readId();

				/**
				if (fLexer.peekOperator(OP.LBRACKET)) {
					fLexer.startCapture();
					fLexer.skipPastMatch("[", "]");
					fLexer.endCapture();
				}
				 */
				
				last_type = type;
			}

			
			SVDBParamPortDecl param_r = new SVDBParamPortDecl(type);
			param_r.setDir(dir);
			param_r.setLocation(it_start);
			
			SVDBVarDeclItem param = new SVDBVarDeclItem(id);
			param_r.addChildItem(param);
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				// This port is an array port
				param.setArrayDim(parsers().dataTypeParser().var_dim());
			}

			params.add(param_r);
			
			if (fLexer.peekOperator(OP.EQ)) {
				fLexer.eatToken();
				param.setInitExpr(parsers().exprParser().expression());
			}
			
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
