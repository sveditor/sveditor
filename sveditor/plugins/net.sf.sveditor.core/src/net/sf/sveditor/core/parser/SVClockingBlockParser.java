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
		String name = "";
		
		clk_blk.setLocation(fLexer.getStartLocation());
		
		parent.addChildItem(clk_blk);

		try {
			String type = null;
			
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
			fLexer.readOperator(";");

			// Global clocking does not have a body
			if (type == null || !type.equals("global")) {
				while (fLexer.peek() != null && !fLexer.peekKeyword("endclocking")) {
					clocking_item(clk_blk);
				}
			}

				/*
			if (fLexer.peekKeyword("default")) {
				fLexer.eatToken();
				String type = fLexer.readKeyword("input", "output");
				// TODO:
				fLexer.readOperator(";");
			} else if (fLexer.peekKeyword("input))
				 */
			clk_blk.setEndLocation(fLexer.getStartLocation());
			fLexer.readKeyword("endclocking");

			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} finally {
		}
	}
	
	private void clocking_item(SVDBClockingBlock clk_blk) throws SVParseException {
		if (fDebugEn) {
			debug("clocking_item: " + fLexer.peek());
		}
		if (fLexer.peekKeyword("default")) {
			// default 
			default_skew();
			fLexer.readOperator(";");
		} else if (fLexer.peekKeyword("input", "output", "inout")) {
			// TODO: Add to AST
			// clocking_direction [clocking_skew] list_of_clocking_decl_assign
			String dir = fLexer.eatToken();
			if (fDebugEn) {
				debug("post-direction: " + fLexer.peek());
			}
			if (fLexer.peekKeyword("posedge","negedge") || fLexer.peekOperator("#")) {
				clocking_skew();
				if (dir.equals("input") && fLexer.peekKeyword("output")) {
					fLexer.eatToken();
					if (fLexer.peekKeyword("posedge","negedge") || fLexer.peekOperator("#")) {
						clocking_skew();
					}
				}
			}

			while (fLexer.peek() != null) {
				fLexer.readId();

				if (fLexer.peekOperator("=")) {
					fLexer.eatToken();
					fParsers.exprParser().expression();
				}

				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}

			fLexer.readOperator(";");
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
		fLexer.readKeyword("default");

		String type = fLexer.readKeyword("input", "output");
		clocking_skew();
		if (type.equals("input") && fLexer.peekKeyword("output")) {
			fLexer.readKeyword("output");
			clocking_skew();
		}
	}

	// TODO: save parsed information
	private void clocking_skew() throws SVParseException {
		if (fLexer.peekKeyword("posedge", "negedge")) {
			fLexer.eatToken();
			if (fLexer.peekOperator("#")) {
				fParsers.exprParser().delay_expr(3);
			}
		} else {
			fParsers.exprParser().delay_expr(3);
		}
	}
	
	@SuppressWarnings("unused")
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
