package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBLocation;


public interface ISVParser {
	
	SVLexer lexer();
	
	// ITextScanner scanner();
	
	void error(SVParseException e) throws SVParseException;
	
	void warning(String msg, int lineno);
	
	boolean error_limit_reached();
	
	SVParsers parsers();
	
}
