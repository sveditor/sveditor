package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.scanutils.ITextScanner;

public interface ISVParser {
	
	SVLexer lexer();
	
	// ITextScanner scanner();
	
	void error(String msg, int lineno);
	
	void warning(String msg, int lineno);
	
	boolean error_limit_reached();
	
	SVParsers parsers();

}
