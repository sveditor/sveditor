/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.SVDBTask;

public class SVTaskFuncBodyParser extends SVParserBase {
	
	public SVTaskFuncBodyParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(SVDBTask tf, boolean is_ansi) throws SVParseException {
		String end_keyword = (tf.getType() == SVDBItemType.Function)?"endfunction":"endtask";
		if (fDebugEn) {
			debug("--> SVTaskFuncBodyParser: " + fLexer.peek());
			debug("SVTaskFuncBodyParse: is_ansi=" + is_ansi);
		}
		
		
		// Parse the task/function body, including declarations
		// decl_allowed tracks the 
		boolean decl_allowed = true;
		while (fLexer.peek() != null) {
			if (fLexer.peekKeyword(end_keyword)) {
				break;
			// check for parameters - these can be used in port lists etc.
			} else if (fLexer.peekKeyword("parameter") || fLexer.peekKeyword("localparam")) {
				parsers().modIfcBodyItemParser().parse_parameter_decl(tf);
			} else if (ParserSVDBFileFactory.isFirstLevelScope(fLexer.peek(), 0)) {
				error("Missing " + ((tf.getType() == SVDBItemType.Function)?"function":"task") + " end");
			} else {
				decl_allowed = parsers().behavioralBlockParser().statement(tf, decl_allowed, is_ansi);
			}
		}
		
		if (fDebugEn) {
			debug("<-- SVTaskFuncBodyParser: " + fLexer.peek());
		}
	}
}
