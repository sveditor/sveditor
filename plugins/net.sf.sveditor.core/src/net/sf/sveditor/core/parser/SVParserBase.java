package net.sf.sveditor.core.parser;



public class SVParserBase implements ISVParser {
	
	protected static final boolean			fDebugEn = false;
	protected ISVParser						fParser;
	
	protected SVParserBase(ISVParser parser) {
		fParser = parser;
	}
	
	public boolean error_limit_reached() {
		return fParser.error_limit_reached();
	}

	public void error(SVParseException e) throws SVParseException {
		fParser.error(e);
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
		if (fDebugEn) {
			System.out.println("Parser: " + msg);
		}
	}
}
