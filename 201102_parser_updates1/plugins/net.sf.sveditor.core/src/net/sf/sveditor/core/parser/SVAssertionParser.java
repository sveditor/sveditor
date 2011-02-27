package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;

public class SVAssertionParser extends SVParserBase {
	
	public SVAssertionParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBAssertStmt parse() throws SVParseException {
		SVDBAssertStmt assert_stmt = new SVDBAssertStmt();
		
		lexer().readKeyword("assert");
		debug("assertion_stmt - " + lexer().peek());

		if (lexer().peekKeyword("property")) {
			lexer().eatToken();
			// TODO: properly implement property expressions 
			lexer().readOperator("(");
			lexer().skipPastMatch("(", ")");
		} else {
			lexer().readOperator("(");
			assert_stmt.setExpr(parsers().exprParser().expression());
			lexer().readOperator(")");
		}

		assert_stmt.setActionBlock(parsers().behavioralBlockParser().action_block());
		
		return assert_stmt;
	}

}
