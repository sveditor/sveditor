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
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

public class SVTaskFunctionPortListParser extends SVParserBase {
	
	public SVTaskFunctionPortListParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBParamPort> parse() throws SVParseException {
		List<SVDBParamPort> params = new ArrayList<SVDBParamPort>();
		int dir = SVDBParamPort.Direction_Input;
		SVDBTypeInfo last_type = null;
		
		lexer().readOperator("(");
		
		// Empty parameter list
		if (lexer().peekOperator(")")) {
			lexer().eatToken();
			return params;
		}
		
		while (true) {
			SVDBLocation it_start = lexer().getStartLocation();
			if (lexer().peekKeyword("input", "output", "inout", "ref")) {
				String dir_s = lexer().eatToken();
				if (dir_s.equals("input")) {
					dir = SVDBParamPort.Direction_Input;
				} else if (dir_s.equals("output")) {
					dir = SVDBParamPort.Direction_Output;
				} else if (dir_s.equals("inout")) {
					dir = SVDBParamPort.Direction_Inout;
				} else if (dir_s.equals("ref")) {
					dir = SVDBParamPort.Direction_Ref;
				}
			} else if (lexer().peekKeyword("const")) {
				lexer().eatToken();
				lexer().readKeyword("ref");
				dir = (SVDBParamPort.Direction_Ref | SVDBParamPort.Direction_Const);
			}
			
			if (lexer().peekKeyword("var")) {
				lexer().eatToken();
				dir |= SVDBParamPort.Direction_Var;
			}
			
			SVDBTypeInfo type = 
				parsers().dataTypeParser().data_type(0);

			// This could be a continuation of the same type: int a, b, c
			if (lexer().peekOperator("[")) {
				lexer().startCapture();
				lexer().skipPastMatch("[", "]");
				lexer().endCapture();
			}

			String id;

			// Handle the case where a single type and a 
			// list of parameters is declared
			if (lexer().peekOperator(",", ")", "=", "[")) {
				// use previous type
				id = type.getName();
				type = last_type;
			} else {

				id = lexer().readId();

				/**
				if (lexer().peekOperator("[")) {
					lexer().startCapture();
					lexer().skipPastMatch("[", "]");
					lexer().endCapture();
				}
				 */
				
				last_type = type;
			}

			
			SVDBParamPort param_r = new SVDBParamPort(type);
			param_r.setDir(dir);
			param_r.setLocation(it_start);
			
			SVDBVarDeclItem param = new SVDBVarDeclItem(id);
			param_r.addVar(param);
			
			if (lexer().peekOperator("[")) {
				// This port is an array port
				param.setArrayDim(parsers().dataTypeParser().var_dim());
			}

			params.add(param_r);
			
			if (lexer().peekOperator("=")) {
				lexer().eatToken();
				param.setInitExpr(parsers().exprParser().expression());
			}
			
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		
		lexer().readOperator(")");
		
		return params;
	}

}
