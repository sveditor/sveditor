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
