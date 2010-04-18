package net.sf.sveditor.core.parser;


public class SVParserBase {
	
	protected static final boolean			fDebugEn = true;
	protected SVLexer						fLexer;
	
	protected SVParserBase(SVLexer lexer) {
		fLexer = lexer;
	}
	
	
	protected void debug(String msg) {
		
	}
}
