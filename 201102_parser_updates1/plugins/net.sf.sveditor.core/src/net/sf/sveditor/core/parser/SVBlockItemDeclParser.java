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
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent, SVDBLocation start) throws SVParseException {
		
		if (fLexer.peekKeyword("typedef")) {
			parsers().dataTypeParser().typedef(parent);
		} else {
			if (start == null) {
				start = fLexer.getStartLocation();
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
			if (((fLexer.peekKeyword(SVKeywords.fBuiltinTypes) || SVKeywords.isDir(fLexer.peek())) && !fLexer.peekKeyword("void")) ||
					!SVKeywords.isSVKeyword(fLexer.peek())) {
				// Data declaration or statement
				SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
				SVDBVarDeclStmt var_decl = new SVDBVarDeclStmt(type, 0);
				var_decl.setLocation(start);
				parent.addChildItem(var_decl);

				// Ensure we don't misinterpret a static reference
				if (!fLexer.peekOperator("::")) {
					while (true) {
						SVDBLocation it_start = fLexer.getStartLocation();
						String name = fLexer.readId();

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
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(";");
				}
			} else {
				error("Unexpected variable-declaration stem token \"" + fLexer.peek() + "\"");
			}
		}
	}
}
