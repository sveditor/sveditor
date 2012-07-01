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
import net.sf.sveditor.core.db.SVDBItem;

public class SVSpecifyBlockParser extends SVParserBase {
	
	public SVSpecifyBlockParser(ISVParser parser) {
		super(parser);
	}

	// TODO: save specify_block info
	public SVDBItem parse(ISVDBAddChildItem parent) throws SVParseException {
		fLexer.readKeyword("specify");
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endspecify")) {
			if (fLexer.peekKeyword("specparam")) {
				error("specify-block specparam unsupported");
			} else if (fLexer.peekKeyword("pulsestyle_onevent", "pulsestyle_ondetect",
					"showcancelled", "noshowcancelled")) {
				error("specify-block pulsestyle_onevent, pulsestyle_ondetect, showcancelled, noshowcancelled unsupported");
			} else if (fLexer.peekOperator("(")) {
				// path_declaration
				path_declaration();
				
				fLexer.readOperator("=");
				list_of_path_delay_expressions();
			}
		}
		
		fLexer.readKeyword("endspecify");
		
		return null;
	}

	// TODO: store data
	private void path_declaration() throws SVParseException {
		int count=0;
		
		fLexer.readOperator("(");
		while (fLexer.peek()  != null) {
			specify_input_terminal_descriptor();
			count++;
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		if (count > 1) {
			fLexer.readOperator("*>");
		} else {
			fLexer.readOperator("=>");
		}
		
		fLexer.readOperator(")");
	}
	
	private void specify_input_terminal_descriptor() throws SVParseException {
		fLexer.readId();
		
		if (fLexer.peekOperator("[")) {
			fLexer.eatToken();
			fParsers.exprParser().const_or_range_expression();
			fLexer.readOperator("]");
		}
	}
	
	private void list_of_path_delay_expressions() throws SVParseException {
		boolean has_paren = fLexer.peekOperator("(");
		
		if (has_paren) {
			fLexer.readOperator("(");
		}
		
		fLexer.readNumber();
		if (fLexer.peekOperator(",")) {
			fLexer.eatToken();
			fLexer.readNumber();
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				fLexer.readNumber();
			}
		}
	
		if (has_paren) {
			fLexer.readOperator(")");
		}
	}
}
