package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssumeStmt;

public class SVAssertionParser extends SVParserBase {
	
	public SVAssertionParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBAssertStmt parse(ISVDBAddChildItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		
		String assert_type = fLexer.readKeyword("assert", "assume");
		SVDBAssertStmt assert_stmt;
		if (assert_type.equals("assert")) {
			assert_stmt = new SVDBAssertStmt();
		} else {
			assert_stmt = new SVDBAssumeStmt();
		}
		assert_stmt.setLocation(start);
		debug("assertion_stmt - " + fLexer.peek());

		if (fLexer.peekKeyword("property")) {
			fLexer.eatToken();
			// TODO: properly implement property expressions 
			fLexer.readOperator("(");
			fLexer.skipPastMatch("(", ")");
		} else {
			fLexer.readOperator("(");
			assert_stmt.setExpr(parsers().exprParser().expression());
			fLexer.readOperator(")");
		}
		
		parent.addChildItem(assert_stmt);
		assert_stmt.setActionBlock(new SVDBActionBlockStmt());

		parsers().behavioralBlockParser().action_block(assert_stmt.getActionBlock());
		
		return assert_stmt;
	}

}
