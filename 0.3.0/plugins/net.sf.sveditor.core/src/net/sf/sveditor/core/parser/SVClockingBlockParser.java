package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBClockingBlock;

public class SVClockingBlockParser extends SVParserBase {
	
	public SVClockingBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBClockingBlock parse() throws SVParseException {
		SVDBClockingBlock clk_blk = new SVDBClockingBlock("");
		String name = "";
		String expr = "";
		
		clk_blk.setLocation(lexer().getStartLocation());
		parsers().SVParser().enter_scope("clocking", clk_blk);

		try {
			// TODO: 
			if (lexer().peekKeyword("default", "global") ) {
				lexer().eatToken();
			}
			lexer().readKeyword("clocking");

			if (!lexer().peekOperator("@")) {
				// Expect a clocking block identifier
				name = lexer().readId();
			}
			clk_blk.setName(name);

			lexer().readOperator("@");
			if (lexer().peekOperator("(")) {
				lexer().eatToken();
				expr = "(";
				expr += event_expr();
				lexer().readOperator(")");
				expr += ")";
			} else {
				expr = lexer().readId();
			}

			while (lexer().peek() != null && !lexer().peekKeyword("endclocking")) {
				parsers().SVParser().scan_statement();

				/*
			if (lexer().peekKeyword("default")) {
				lexer().eatToken();
				String type = lexer().readKeyword("input", "output");
				// TODO:
				lexer().readOperator(";");
			} else if (lexer().peekKeyword("input))
				 */
			}

			clk_blk.setEndLocation(lexer().getStartLocation());
			lexer().readKeyword("endclocking");

			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
		} finally {
			parsers().SVParser().handle_leave_scope();
		}
		
		return clk_blk;
	}
	
	private String event_expr() throws SVParseException {
		String ret = null;
		
		try {
			while (lexer().peek() != null) {
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					if (lexer().peekKeyword("posedge","negedge","event")) {
						lexer().eatToken();
					}
					lexer().readId();
				}
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else if (lexer().peekKeyword("or")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} finally {
			ret = lexer().endCapture();
		}
	
		return ret;
	}

}
