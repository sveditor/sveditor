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

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoBuiltin;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.scanner.SVKeywords;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}

	public void parse(ISVDBAddChildItem parent, SVDBTypeInfo type, long start) throws SVParseException {
		parse(parent, type, start, true);
	}

	public void parse(ISVDBAddChildItem parent, SVDBTypeInfo type, long start, boolean consume_terminator) throws SVParseException {
		
		if (fLexer.peekKeyword(KW.TYPEDEF)) {
			parsers().dataTypeParser().typedef(parent);
		} else {
			String dir = null;
			if (start == -1) {
				start = fLexer.getStartLocation();
			}
			if (fLexer.peekKeyword(KW.INPUT, KW.OUTPUT, KW.INOUT)) {
				// TODO: add qualifiers to variable
				dir = fLexer.eatTokenR();
			}
			// TODO: add qualifiers to variable
			if (fLexer.peekKeyword(KW.CONST)) {
				fLexer.eatToken();
			}
			if (fLexer.peekKeyword(KW.VAR)) {
				fLexer.eatToken();
			}

			if (fLexer.peekKeyword(KW.STATIC, KW.AUTOMATIC)) {
				fLexer.eatToken();
			}

			// Should be the data-type
			// String id = fLexer.eatTokenR();
			if (((fLexer.peekKeyword(SVKeywords.fBuiltinTypesE)) && !fLexer.peekKeyword(KW.VOID)) ||
					!SVKeywords.isSVKeyword(fLexer.peek()) || 
					fLexer.peekKeyword(KW.STRUCT,KW.UNION,KW.ENUM,KW.VIRTUAL)) {
				String name = null;
				// Data declaration or statement
				if (type == null) {
					type = parsers().dataTypeParser().data_type(0);
				}
				
				if (fDebugEn) {
					debug("type=" + type + " " + fLexer.peek());
				}
				
				// Allow for untyped parameters
				if (dir != null && fLexer.peekOperator()) {
					name = type.getName();
					type = new SVDBTypeInfoBuiltin(dir);
				}
				
				SVDBVarDeclStmt var_decl = new SVDBVarDeclStmt(type, 0);
				var_decl.setLocation(start);
				parent.addChildItem(var_decl);

				// Ensure we don't misinterpret a static reference
				if (!fLexer.peekOperator(OP.COLON2)) {
					while (fLexer.peek() != null) {
						long it_start = fLexer.getStartLocation();
						if (name == null) {
							name = fLexer.readId();
						}

						SVDBVarDeclItem var = new SVDBVarDeclItem(name);
						var.setLocation(it_start);

						var_decl.addChildItem(var);

						// TODO: handle array, queue, etc
						if (fLexer.peekOperator(OP.LBRACKET)) {
							var.setArrayDim(parsers().dataTypeParser().var_dim());
						}

						if (fLexer.peekOperator(OP.EQ)) {
							fLexer.eatToken();
							var.setInitExpr(parsers().exprParser().expression());
						}

						if (fLexer.peekOperator(OP.COMMA)) {
							// Could be:
							// => , <var_id>
							// => <type_id> <var_id>
							// => 
							// Want to continue only if post-comma token is an identifer and 
							// post-post token is not an identifier
							SVToken comma_tok = fLexer.consumeToken();
							SVToken post_var = fLexer.consumeToken();
							SVToken post_post_var = fLexer.consumeToken();
							
							if (post_var != null && post_var.isIdentifier() &&
									post_post_var != null && !post_post_var.isIdentifier()) {
								fLexer.ungetToken(post_post_var);
								fLexer.ungetToken(post_var);
							} else {
								fLexer.ungetToken(post_post_var);
								fLexer.ungetToken(post_var);
								fLexer.ungetToken(comma_tok);
								break;
							}
						} else {
							break;
						}
						name = null;
					}
					if (consume_terminator) {
						fLexer.readOperator(OP.SEMICOLON);
					}
				}
			} else {
				error("Unexpected variable-declaration stem token \"" + fLexer.peek() + "\"");
			}
		}
	}
}
