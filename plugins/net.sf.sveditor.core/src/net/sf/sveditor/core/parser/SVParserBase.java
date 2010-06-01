package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.scanutils.ITextScanner;


public class SVParserBase implements ISVParser {
	
	protected static final boolean			fDebugEn = true;
	protected ISVParser						fParser;
	
	protected SVParserBase(ISVParser parser) {
		fParser = parser;
	}
	
	public boolean error_limit_reached() {
		return fParser.error_limit_reached();
	}

	public void error(String msg, int lineno) {
		fParser.error(msg, lineno);
	}

	public SVLexer lexer() {
		return fParser.lexer();
	}

	public void warning(String msg, int lineno) {
		fParser.warning(msg, lineno);
	}
	
	public SVParsers parsers() {
		return fParser.parsers();
	}

	protected void debug(String msg) {
		
	}
}
