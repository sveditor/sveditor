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

public class SVSpecifyBlockParser extends SVParserBase {
	
	public SVSpecifyBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBItem parse() throws SVParseException {
		lexer().readKeyword("specify");
		
		while (lexer().peek() != null && !lexer().peekKeyword("endspecify")) {
			parsers().SVParser().scan_statement();
		}
		
		lexer().readKeyword("endspecify");
		
		return null;
	}

}
