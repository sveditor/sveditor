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

import net.sf.sveditor.core.db.SVDBItem;

public class SVBehavioralBlockParser extends SVParserBase {
	
	public SVBehavioralBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBItem parse() throws SVParseException {
		SVDBItem ret = null;
		
		if (lexer().peekKeyword("begin")) {
			// begin/end block
			lexer().skipPastMatch("begin", "end");
			/*
			lexer().eatToken();
			if (lexer().peekOperator(":")) {
				// named begin
				lexer().eatToken();
				lexer().readId();
			}
			 */
		} else {
			parsers().SVParser().scan_statement();
		}
		
		return ret;
	}

}
