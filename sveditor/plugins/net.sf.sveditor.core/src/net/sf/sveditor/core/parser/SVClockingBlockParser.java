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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBClockingBlock;

public class SVClockingBlockParser extends SVParserBase {
	
	public SVClockingBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		SVDBClockingBlock clk_blk = new SVDBClockingBlock("");
		String name = null;
		
		clk_blk.setLocation(fLexer.getStartLocation());
		
		parent.addChildItem(clk_blk);

		try {
			String type = null;
			
			// TODO: 
			if (fLexer.peekKeyword(KW.DEFAULT, KW.GLOBAL)) {
				type = fLexer.eatTokenR();
			}
			fLexer.readKeyword(KW.CLOCKING);

			if (!fLexer.peekOperator(OP.AT)) {
				// Expect a clocking block identifier
				name = fLexer.readId();
				clk_blk.setName(name);
			} else {
				clk_blk.setName("");
			}
		
			// Section 14.12: reference to a previously-defined clocking block
			if (name != null && fLexer.peekOperator(OP.SEMICOLON)) {
				fLexer.eatToken();
			} else {

				clk_blk.setExpr(fParsers.exprParser().clocking_event());
				fLexer.readOperator(OP.SEMICOLON);

				// Global clocking does not have a body
				if (type == null || !type.equals("global")) {
					while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDCLOCKING)) {
						clocking_item(clk_blk);
					}
				}

				clk_blk.setEndLocation(fLexer.getStartLocation());
				fLexer.readKeyword(KW.ENDCLOCKING);

				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId();
				}
			}
		} finally {
		}
	}
	
	private void clocking_item(SVDBClockingBlock clk_blk) throws SVParseException {
		if (fDebugEn) {
			debug("clocking_item: " + fLexer.peek());
		}
		if (fLexer.peekKeyword(KW.DEFAULT)) {
			// default 
			default_skew();
			fLexer.readOperator(OP.SEMICOLON);
		} else if (fLexer.peekKeyword(KW.INPUT, KW.OUTPUT, KW.INOUT)) {
			// TODO: Add to AST
			// clocking_direction [clocking_skew] list_of_clocking_decl_assign
			String dir = fLexer.eatTokenR();
			if (fDebugEn) {
				debug("post-direction: " + fLexer.peek());
			}
			if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE) || fLexer.peekOperator(OP.HASH)) {
				clocking_skew();
				if (dir.equals("input") && fLexer.peekKeyword(KW.OUTPUT)) {
					fLexer.eatToken();
					if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE) || fLexer.peekOperator(OP.HASH)) {
						clocking_skew();
					}
				}
			}

			while (fLexer.peek() != null) {
				fLexer.readId();

				if (fLexer.peekOperator(OP.EQ)) {
					fLexer.eatToken();
					fParsers.exprParser().expression();
				}

				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}

			fLexer.readOperator(OP.SEMICOLON);
		} else {
			// {attribute_instance} assertion_item_declaration
			fParsers.attrParser().parse(null);
			assertion_item_declaration(clk_blk);
		}
	}
	
	private void assertion_item_declaration(ISVDBAddChildItem parent) throws SVParseException {
		String type = fLexer.peek();
		if (type.equals("property")) {
			fParsers.propertyParser().property(parent);
		} else if (type.equals("sequence")) {
			fParsers.sequenceParser().sequence(parent);
		} else if (type.equals("let")) {
			error("let construct unsupported");
		} else {
			error("Unknown assertion_item_declaration item: " + type);
		}
	}

	// TODO: save parsed information
	private void default_skew() throws SVParseException {
		fLexer.readKeyword(KW.DEFAULT);

		KW type = fLexer.readKeyword(KW.INPUT, KW.OUTPUT);
		clocking_skew();
		if (type == KW.INPUT && fLexer.peekKeyword(KW.OUTPUT)) {
			fLexer.eatToken();
			clocking_skew();
		}
	}

	// TODO: save parsed information
	private void clocking_skew() throws SVParseException {
		if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE)) {
			fLexer.eatToken();
			if (fLexer.peekOperator(OP.HASH)) {
				fParsers.exprParser().delay_expr(3);
			}
		} else {
			fParsers.exprParser().delay_expr(3);
		}
	}
	
	@SuppressWarnings("unused")
	private String event_expr() throws SVParseException {
		String ret = null;
		
		while (fLexer.peek() != null) {
			if (fLexer.peekOperator(OP.LPAREN)) {
				fLexer.skipPastMatch("(", ")");
			} else {
				if (fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE, KW.EVENT)) {
					fLexer.eatToken();
				}
				fLexer.readId();
			}
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else if (fLexer.peekKeyword(KW.OR)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}

		return ret;
	}

}
