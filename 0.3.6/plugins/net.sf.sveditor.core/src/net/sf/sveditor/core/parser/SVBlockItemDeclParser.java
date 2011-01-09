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

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBItem> parse(String id) throws SVParseException {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		if (id.equals("const")) {
			id = lexer().eatToken();
		}
		if (id.equals("var")) {
			id = lexer().eatToken();
		}

		if (id.equals("static") || id.equals("automatic")) {
			id = lexer().eatToken();
		}
		
		// Should be the data-type
		// String id = lexer().eatToken();
		if (((SVKeywords.isBuiltInType(id) || SVKeywords.isDir(id)) && !id.equals("void")) ||
				!SVKeywords.isSVKeyword(id)) {
			// Data declaration or statement
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0, id);

			// Ensure we don't misinterpret a static reference
			if (!lexer().peekOperator("::")) {
				while (true) {
					SVDBLocation it_start = lexer().getStartLocation();
					String name = lexer().readId();
				
					SVDBVarDeclItem var = new SVDBVarDeclItem(type, name, 0);
					var.setLocation(it_start);
				
					ret.add(var);

					// TODO: handle array, queue, etc
					if (lexer().peekOperator("[")) {
						lexer().eatToken();
						
						// array or queue
						if (lexer().peekOperator("$")) {
							// queue
							lexer().eatToken();
							lexer().readOperator("]");
						} else if (lexer().peekOperator("]")) {
							lexer().readOperator("]");
						} else {
							// bounded array
							lexer().skipPastMatch("[", "]");
						}
					}

					if (lexer().peekOperator("=")) {
						// TODO: eat tokens until ',' or ';'
						lexer().eatToken();
						parsers().exprParser().expression();
					}
				
					if (lexer().peekOperator(",")) {
						lexer().eatToken();
					} else {
						break;
					}
				}
				lexer().readOperator(";");
			}
		} else if (id.equals("typedef")) {
			for (SVDBTypedef td : parsers().SVParser().process_typedef(true)) {
				ret.add(td);
			}
		} else {
			error("Unexpected variable-declaration stem token \"" + id + "\"");
		}
		
		return ret;
	}
}
