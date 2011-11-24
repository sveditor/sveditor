/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBProperty;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVPropertyParser extends SVParserBase {
	
	public SVPropertyParser(ISVParser parser) {
		super(parser);
	}

	///////////////////////////////////////////////////////////////////////////////////////////////////
	//	property_declaration ::= 
	//			property property_identifier [ ( [ tf_port_list ] ) ] ; 
	//			{ assertion_variable_declaration } 
	//			property_spec ; 
	//			endproperty [ : property_identifier ] 
	//			list_of_formals ::= formal_list_item { , formal_list_item } 
	//			property_spec ::= 
	//			[clocking_event ] [ disable iff ( expression_or_dist ) ] property_expr 
	//			property_expr ::= 
	//			sequence_expr 
	//			| ( property_expr ) 
	//			| not property_expr 
	//			| property_expr or property_expr 
	//			| property_expr and property_expr 
	//			| sequence_expr |-> property_expr 
	//			| sequence_expr |=> property_expr 
	//			| if ( expression_or_dist ) property_expr [ else property_expr ] 
	//			| property_instance 
	//			| clocking_event property_expr 
	//			assertion_variable_declaration ::= 
	//			var_data_type list_of_variable_identifiers ; 
	//			property_instance::= 
	//			ps_property_identifier [ ( [ list_of_arguments ] ) ] 
	///////////////////////////////////////////////////////////////////////////////////////////////////
	public void property(ISVDBAddChildItem parent) throws SVParseException {
		SVDBProperty prop = new SVDBProperty();
		
		// Parse the following:
		// property property_name [(some_parameter_list, and_another_parameter)];
		fLexer.readKeyword("property");
		
		prop.setName(fLexer.readId());
		
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			if (!fLexer.peekOperator(")")) {
				while (fLexer.peek() != null) {
					prop.addPropertyPort(property_port_item());

					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(")");
			// TODO: argument list
		}
		fLexer.readOperator(";");
		
		parent.addChildItem(prop);

		// data declarations
		while (fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes) || fLexer.peekKeyword("var") || fLexer.isIdentifier()) {
			SVDBLocation start = fLexer.getStartLocation();
			if (fLexer.peekKeyword("var") || fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes)) {
				// Definitely a declaration
				parsers().blockItemDeclParser().parse(prop, null, start);
			} else {
				// May be a declaration. Let's see
				// pkg::cls #(P)::field = 2; 
				// pkg::cls #(P)::type var;
				// field.foo
				SVToken tok = fLexer.consumeToken();
				
				if (fLexer.peekOperator("::","#") || fLexer.peekId()) {
					// Likely to be a declaration. Let's read a type
					fLexer.ungetToken(tok);
					final List<SVToken> tok_l = new ArrayList<SVToken>();
					ISVTokenListener l = new ISVTokenListener() {
						public void tokenConsumed(SVToken tok) {
							tok_l.add(tok);
						}
						public void ungetToken(SVToken tok) {
							tok_l.remove(tok_l.size()-1);
						}
					}; 
					SVDBTypeInfo type = null;
					try {
						fLexer.addTokenListener(l);
						type = parsers().dataTypeParser().data_type(0);
					} finally {
						fLexer.removeTokenListener(l);
					}

					// Okay, what's next?
					if (fLexer.peekId()) {
						// Conclude that this is a declaration
						debug("Assume a declaration @ " + fLexer.peek());
						parsers().blockItemDeclParser().parse(prop, type, start);
					} else {
						debug("Assume a typed reference @ " + fLexer.peek());
						// Else, this is probably a typed reference
						fLexer.ungetToken(tok_l);
						break;
					}
				} else {
					// More likely to not be a type
					fLexer.ungetToken(tok);
					break;
				}
			}
		}

		// Check if property has an clocking / event term
		if (lexer().peekOperator("@")) {
			// Possibly a clocking event which is @
			parsers().exprParser().clocking_event();
		}

		// Check for disable iff (...)
		if (fLexer.peekKeyword("disable"))  {
			fLexer.readKeyword("disable");
			fLexer.readKeyword("iff");
			fLexer.readOperator("(");
			// TODO: Figure out what to do with this
			SVDBExprStmt stmt = new SVDBExprStmt();
			stmt.setLocation(fLexer.getStartLocation());
			stmt.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
		}
		
		try {
			property_statement_spec(prop);
		} finally {
			prop.setEndLocation(fLexer.getStartLocation());
		}

		fLexer.readKeyword("endproperty");
		
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}
	}

	private void property_statement_spec(SVDBProperty prop) throws SVParseException {
		if (fLexer.peekKeyword("case")) {
			// TODO:
		} else if (fLexer.peekKeyword("if")) {
			// TODO:
		} else {
			// Expression
			SVDBExprStmt stmt = new SVDBExprStmt();
			stmt.setLocation(fLexer.getStartLocation());
			stmt.setExpr(fParsers.propertyExprParser().property_expr());
			fLexer.readOperator(";");
		}
	}
	
	private SVDBParamPortDecl property_port_item() throws SVParseException {
		int attr = 0;
		SVDBParamPortDecl port = new SVDBParamPortDecl();
		port.setLocation(fLexer.getStartLocation());
		if (fLexer.peekKeyword("local")) {
			fLexer.eatToken();
			// TODO: save local as an attribute
			if (fLexer.peekKeyword("input")) {
				fLexer.eatToken();
				attr |= SVDBParamPortDecl.Direction_Input;
			}
		}
		port.setAttr(attr);
		
		if (fLexer.peekKeyword("sequence","event","untyped","property")) {
			port.setTypeInfo(new SVDBTypeInfoBuiltin(fLexer.eatToken()));
		} else {
			if (fLexer.peekId()) {
				SVToken t = fLexer.consumeToken();
				if (fLexer.peekId()) {
					fLexer.ungetToken(t);
					port.setTypeInfo(fParsers.dataTypeParser().data_type(0));
				} else {
					// implicit type
					fLexer.ungetToken(t);
				}
			} else {
				// data_type_or_implicit
				port.setTypeInfo(fParsers.dataTypeParser().data_type(0));
			}
		}
		SVDBVarDeclItem vi = new SVDBVarDeclItem();
		vi.setLocation(fLexer.getStartLocation());
		vi.setName(fLexer.readId());
		port.addChildItem(vi);
		
		if (fLexer.peekOperator("[")) {
			vi.setArrayDim(fParsers.dataTypeParser().var_dim());
		}
		
		if (fLexer.peekOperator("=")) {
			fLexer.eatToken();
			vi.setInitExpr(fParsers.exprParser().expression());
		}
		
		return port;
	}
	
}


