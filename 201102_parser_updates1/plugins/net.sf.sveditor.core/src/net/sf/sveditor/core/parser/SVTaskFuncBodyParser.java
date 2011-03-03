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

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVTaskFuncBodyParser extends SVParserBase {
	
	public SVTaskFuncBodyParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(SVDBTaskFuncScope tf, boolean is_ansi) throws SVParseException {
		String end_keyword = (tf.getType() == SVDBItemType.Function)?"endfunction":"endtask";
		debug("--> SVTaskFuncBodyParser: " + lexer().peek());
		
		debug("SVTaskFuncBodyParse: is_ansi=" + is_ansi);
		
		// Parse the task/function body, including declarations
		// decl_allowed tracks the 
		boolean decl_allowed = true;
		while (lexer().peek() != null) {
			if (lexer().peekKeyword(end_keyword)) {
				break;
			} else if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0)) {
				error("Missing " + ((tf.getType() == SVDBItemType.Function)?"function":"task") + " end");
			} else {
				SVDBStmt stmt = parsers().behavioralBlockParser().statement(decl_allowed, is_ansi);
				
				decl_allowed = SVBehavioralBlockParser.isDeclAllowed(stmt);
				
				tf.addItem(stmt);
			}
		}
		
		debug("<-- SVTaskFuncBodyParser: " + lexer().peek());
	}
}
