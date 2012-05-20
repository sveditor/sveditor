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
import net.sf.sveditor.core.db.SVDBClockingBlock;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVClockingBlockParser extends SVParserBase {
	
	public SVClockingBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		SVDBClockingBlock clk_blk = new SVDBClockingBlock("");
		String name = "";
		
		clk_blk.setLocation(fLexer.getStartLocation());
		
		parent.addChildItem(clk_blk);

		try {
			String type = "";
			
			// TODO: 
			if (fLexer.peekKeyword("default", "global") ) {
				type = fLexer.eatToken();
			}
			fLexer.readKeyword("clocking");

			if (!fLexer.peekOperator("@")) {
				// Expect a clocking block identifier
				name = fLexer.readId();
			}
			clk_blk.setName(name);

			clk_blk.setExpr(fParsers.exprParser().clocking_event());

			while (fLexer.peek() != null && !fLexer.peekKeyword("endclocking")) {
				parsers().SVParser().scan_statement();

				/*
			if (fLexer.peekKeyword("default")) {
				fLexer.eatToken();
				String type = fLexer.readKeyword("input", "output");
				// TODO:
				fLexer.readOperator(";");
			} else if (fLexer.peekKeyword("input))
				 */
			}

			clk_blk.setEndLocation(fLexer.getStartLocation());
			fLexer.readKeyword("endclocking");

			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} finally {
		}
	}
	
	private String event_expr() throws SVParseException {
		String ret = null;
		
		try {
			while (fLexer.peek() != null) {
				if (fLexer.peekOperator("(")) {
					fLexer.skipPastMatch("(", ")");
				} else {
					if (fLexer.peekKeyword("posedge","negedge","event")) {
						fLexer.eatToken();
					}
					fLexer.readId();
				}
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else if (fLexer.peekKeyword("or")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} finally {
			ret = fLexer.endCapture();
		}
	
		return ret;
	}

}
