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

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVTaskFuncBodyParser extends SVParserBase {
	
	public SVTaskFuncBodyParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(SVDBTaskFuncScope tf, boolean is_ansi) throws SVParseException {
		String decl_keywords[];
		String decl_keywords_ansi[] = {"const", "var", "automatic", "static", "typedef"};
		String decl_keywords_nonansi[] = {"const", "var", "automatic", "static", "typedef", "input", "output", "inout", "ref"};
		String end_keyword = (tf.getType() == SVDBItemType.Function)?"endfunction":"endtask";
		debug("--> SVTaskFuncBodyParser: " + lexer().peek());
		
		debug("SVTaskFuncBodyParse: is_ansi=" + is_ansi);
		
		decl_keywords = (is_ansi)?decl_keywords_ansi:decl_keywords_nonansi;
		
		// parse declarations first. If non-ansi, port declarations are okay too
		String id = null;
		while (true) {
			id = null;
			try {
				if (lexer().peekKeyword(decl_keywords) || 
						(SVKeywords.isBuiltInType(lexer().peek()) && !lexer().peekKeyword("void")) ||
						lexer().isIdentifier()) {
					
					// Variable declarations
					id = lexer().eatToken(); // should be beginning of type declaration
					
					if ((lexer().peekKeyword() && !lexer().peekKeyword(decl_keywords_nonansi)) ||
							(lexer().peekOperator() && !lexer().peekOperator("#"))) {
						// likely a statement
						break;
					}

					debug("Pre-var parse: " + id);
					List<ISVDBChildItem> vars = parsers().blockItemDeclParser().parse(id);
					debug("Result is " + vars.size() + " vars");
					tf.addItems(vars);
				} else if (lexer().peekKeyword("typedef")) {
					// TODO: permit local type declaration
					break;
				} else {
					// time to move on to the body
					debug("time to move on: " + lexer().peek());
					break;
				}
			} catch (SVParseException e) {
				// Try to recover
				while (lexer().peek() != null && 
						!lexer().peekOperator(";") && !lexer().peekKeyword()) {
					lexer().eatToken();
				}
				if (lexer().peekOperator(";")) {
					lexer().eatToken();
				}
			}
		}

		// now the task/function function body
		// this is much
		while (lexer().peek() != null) {
			if (lexer().peekKeyword(end_keyword)) {
				break;
			} else if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0)) {
				error("Missing " + ((tf.getType() == SVDBItemType.Function)?"function":"task") + " end");
			} else {
				parsers().behavioralBlockParser().parse();
				// id = lexer().eatToken();
			}
		}
		
		debug("<-- SVTaskFuncBodyParser: " + lexer().peek());
	}
}
