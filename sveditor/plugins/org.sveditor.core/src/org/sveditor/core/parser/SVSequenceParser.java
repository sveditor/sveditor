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


package org.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.ISVDBAddChildItem;
import org.sveditor.core.db.SVDBSequence;
import org.sveditor.core.db.SVDBTypeInfo;
import org.sveditor.core.db.SVDBTypeInfoBuiltin;
import org.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.sveditor.core.scanner.SVKeywords;
public class SVSequenceParser extends SVParserBase {
	
	public SVSequenceParser(ISVParser parser) {
		super(parser);
	}
	
	public void sequence(ISVDBAddChildItem parent) throws SVParseException {
		if (fDebugEn) { debug("--> sequence " + fLexer.peek()); }
		SVDBSequence seq = new SVDBSequence();
		seq.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.SEQUENCE);
		
		// Sequence name
		seq.setName(fLexer.readId());
		
		// Port list
		if (fLexer.peekOperator(OP.LPAREN)) {
			// sequence_port_list
			fLexer.eatToken();
			if (!fLexer.peekOperator(OP.RPAREN)) {
				while (fLexer.peek() != null) {
					seq.addPort(sequence_port_item());
					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(OP.RPAREN);
		}
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(seq);
	
		KW kw = fLexer.peekKeywordE();
		boolean is_var_or_builtin =
				(SVKeywords.fBuiltinDeclTypesE.contains(kw) || kw == KW.VAR);
		
		// data declarations
		while (is_var_or_builtin || fLexer.isIdentifier()) {
			long start = fLexer.getStartLocation();
			if (is_var_or_builtin) {
				// Definitely a declaration
				parsers().blockItemDeclParser().parse(seq, null, start);
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
						parsers().blockItemDeclParser().parse(seq, type, start);
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
			
			kw = fLexer.peekKeywordE();
			is_var_or_builtin =
				(SVKeywords.fBuiltinDeclTypesE.contains(kw) || kw == KW.VAR);
		}
		
		// Expression
		seq.setExpr(fParsers.propertyExprParser().sequence_expr());
		
		fLexer.readOperator(OP.SEMICOLON);
		
		fLexer.readKeyword(KW.ENDSEQUENCE);
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fLexer.readId();
		}
		if (fDebugEn) { debug("<-- sequence " + fLexer.peek()); }
	}

	private SVDBParamPortDecl sequence_port_item() throws SVParseException {
		int attr = 0;
		SVDBParamPortDecl port = new SVDBParamPortDecl();
		port.setLocation(fLexer.getStartLocation());
		if (fLexer.peekKeyword(KW.LOCAL)) {
			fLexer.eatToken();
			// TODO: save local as an attribute
			KW kw = fLexer.peekKeywordE();
			if (kw == KW.INPUT) {
				fLexer.eatToken();
				attr |= SVDBParamPortDecl.Direction_Input;
			} else if (kw == KW.INOUT) {
				fLexer.eatToken();
				attr |= SVDBParamPortDecl.Direction_Inout;
			} else if (kw == KW.OUTPUT) {
				fLexer.eatToken();
				attr |= SVDBParamPortDecl.Direction_Output;
			}
		}
		port.setAttr(attr);
		
		if (fLexer.peekKeyword(KW.SEQUENCE, KW.EVENT, KW.UNTYPED)) {
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
