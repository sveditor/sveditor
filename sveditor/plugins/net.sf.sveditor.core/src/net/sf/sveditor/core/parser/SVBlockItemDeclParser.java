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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}

	public void parse(ISVDBAddChildItem parent, SVDBTypeInfo type, SVDBLocation start) throws SVParseException {
		parse(parent, type, start, true);
	}

	public void parse(ISVDBAddChildItem parent, SVDBTypeInfo type, SVDBLocation start, boolean consume_terminator) throws SVParseException {
		
		if (fLexer.peekKeyword("typedef")) {
			parsers().dataTypeParser().typedef(parent);
		} else {
			String dir = null;
			if (start == null) {
				start = fLexer.getStartLocation();
			}
			if (fLexer.peekKeyword("input","output","inout")) {
				// TODO: add qualifiers to variable
				dir = fLexer.eatToken();
			}
			// TODO: add qualifiers to variable
			if (fLexer.peekKeyword("const")) {
				fLexer.eatToken();
			}
			if (fLexer.peekKeyword("var")) {
				fLexer.eatToken();
			}

			if (fLexer.peekKeyword("static", "automatic")) {
				fLexer.eatToken();
			}

			// Should be the data-type
			// String id = fLexer.eatToken();
			if (((fLexer.peekKeyword(SVKeywords.fBuiltinTypes)) && !fLexer.peekKeyword("void")) ||
					!SVKeywords.isSVKeyword(fLexer.peek()) || 
					fLexer.peekKeyword("struct","union","enum","virtual")) {
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
				if (!fLexer.peekOperator("::")) {
					while (fLexer.peek() != null) {
						SVDBLocation it_start = fLexer.getStartLocation();
						if (name == null) {
							name = fLexer.readId();
						}

						SVDBVarDeclItem var = new SVDBVarDeclItem(name);
						var.setLocation(it_start);

						var_decl.addChildItem(var);

						// TODO: handle array, queue, etc
						if (fLexer.peekOperator("[")) {
							var.setArrayDim(parsers().dataTypeParser().var_dim());
						}

						if (fLexer.peekOperator("=")) {
							fLexer.eatToken();
							var.setInitExpr(parsers().exprParser().expression());
						}

						if (fLexer.peekOperator(",")) {
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
						fLexer.readOperator(";");
					}
				}
			} else {
				error("Unexpected variable-declaration stem token \"" + fLexer.peek() + "\"");
			}
		}
	}
}
