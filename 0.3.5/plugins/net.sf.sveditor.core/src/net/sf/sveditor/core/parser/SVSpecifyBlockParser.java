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
