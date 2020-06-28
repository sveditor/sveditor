/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBProperty;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoBuiltin;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExprStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.scanner.SVKeywords;

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
		prop.setLocation(fLexer.getStartLocation());
		
		// Parse the following:
		// property property_name [(some_parameter_list, and_another_parameter)];
		fLexer.readKeyword(KW.PROPERTY);
		
		prop.setName(fLexer.readId());
		// Port List
		if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.eatToken();
			if (!fLexer.peekOperator(OP.RPAREN)) {
				while (fLexer.peek() != null) {
					prop.addPropertyPort(property_port_item());

					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(OP.RPAREN);
			// TODO: argument list
		}
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(prop);

		// data declarations
		while (
				SVKeywords.fBuiltinDeclTypesE.contains(fLexer.peekKeywordE()) || 
				fLexer.peekKeyword(KW.VAR) || fLexer.isIdentifier()) {
			long start = fLexer.getStartLocation();
			// Variable (logic, int unsigned etc)
			if (fLexer.peekKeyword(KW.VAR) || 
					SVKeywords.fBuiltinDeclTypesE.contains(fLexer.peekKeywordE())) {
				// Definitely a declaration
				parsers().blockItemDeclParser().parse(prop, null, start);
			} else {
				// May be a declaration. Let's see
				// pkg::cls #(P)::field = 2; 
				// pkg::cls #(P)::type var;
				// field.foo
				SVToken tok = fLexer.consumeToken();
				
				if (fLexer.peekOperator(OP.COLON2, OP.HASH) || fLexer.peekId()) {
					// Likely to be a declaration. Let's read a type
					fLexer.ungetToken(tok);
					final List<SVToken> tok_l = new ArrayList<SVToken>();
					ISVTokenListener l = new ISVTokenListener() {
						public void tokenConsumed(SVToken tok) {
							tok_l.add(tok.duplicate());
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
						if (fDebugEn) {
							debug("Assume a declaration @ " + fLexer.peek());
						}
						parsers().blockItemDeclParser().parse(prop, type, start);
					} else {
						if (fDebugEn) {
							debug("Assume a typed reference @ " + fLexer.peek());
						}
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
		if (lexer().peekOperator(OP.AT)) {
			// Possibly a clocking event which is @
			parsers().exprParser().clocking_event();
		}

		// Check for disable iff (...)
		if (fLexer.peekKeyword(KW.DISABLE))  {
			fLexer.eatToken();
			fLexer.readKeyword(KW.IFF);
			fLexer.readOperator(OP.LPAREN);
			// TODO: Figure out what to do with this
			SVDBExprStmt stmt = new SVDBExprStmt();
			stmt.setLocation(fLexer.getStartLocation());
			stmt.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(OP.RPAREN);
		}
		
		try {
			property_statement_spec(prop);
		} finally {
			prop.setEndLocation(fLexer.getStartLocation());
		}

		fLexer.readKeyword(KW.ENDPROPERTY);
		
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fLexer.readId();
		}
	}

	/**
	 * property_statement
	 * 
	 * This where the processing of the body of a property statement occurs
	 * the @clocking , disable iff etc are done before this
	 * 
	 * @param prop
	 * @throws SVParseException
	 */
	private void property_statement_spec(SVDBProperty prop) throws SVParseException {
		if (fDebugEn) {
			debug("--> property_statement_spec " + fLexer.peek());
		}
		SVDBExprStmt stmt = new SVDBExprStmt();
		stmt.setLocation(fLexer.getStartLocation());
		stmt.setExpr(fParsers.propertyExprParser().property_statement());
		// If statements may or may not have a trailing semicolon, but will have one if it is
		// here in the "root"
		if (stmt.getExpr() != null && stmt.getExpr().getType() == SVDBItemType.PropertyIfStmt)  {
//		if (stmt.getExpr().getType() == SVDBItemType.PropertyIfStmt)  {
			fLexer.readOperator(OP.SEMICOLON);		
		}
		prop.addChildItem(stmt);
				
		if (fDebugEn) {
			debug("<-- property_statement_spec " + fLexer.peek());
		}
	}
	
	private SVDBParamPortDecl property_port_item() throws SVParseException {
		int attr = 0;
		SVDBParamPortDecl port = new SVDBParamPortDecl();
		port.setLocation(fLexer.getStartLocation());
		if (fLexer.peekKeyword(KW.LOCAL)) {
			fLexer.eatToken();
			// TODO: save local as an attribute
			if (fLexer.peekKeyword(KW.INPUT)) {
				fLexer.eatToken();
				attr |= SVDBParamPortDecl.Direction_Input;
			}
		}
		port.setAttr(attr);
	
		KW kw;
		if ((kw = fLexer.peekKeywordE()) != null &&
				(kw == KW.SEQUENCE || kw == KW.EVENT || kw == KW.UNTYPED || kw == KW.PROPERTY)) {
			port.setTypeInfo(new SVDBTypeInfoBuiltin(fLexer.eatTokenR()));
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
		
		if (fLexer.peekOperator(OP.LBRACKET)) {
			vi.setArrayDim(fParsers.dataTypeParser().var_dim());
		}
		
		if (fLexer.peekOperator(OP.EQ)) {
			fLexer.eatToken();
			vi.setInitExpr(fParsers.exprParser().expression());
		}
		
		return port;
	}
	
}


