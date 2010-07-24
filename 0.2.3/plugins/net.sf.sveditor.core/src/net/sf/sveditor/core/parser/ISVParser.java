package net.sf.sveditor.core.parser;



public interface ISVParser {
	
	SVLexer lexer();
	
	// ITextScanner scanner();
	
	void error(String msg) throws SVParseException;
	
	void error(SVParseException e) throws SVParseException;
	
	void warning(String msg, int lineno);
	
	boolean error_limit_reached();
	
	SVParsers parsers();
	
	void debug(String msg);
	
}
