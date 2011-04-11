package net.sf.sveditor.core.expr_utils;

import net.sf.sveditor.core.parser.ISVParser;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.parser.SVParsers;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVExprUtilsParser implements ISVParser {
	private SVLexer			fLexer;
	private SVParsers		fParsers;
	
	public SVExprUtilsParser(SVExprContext context) {
		fLexer = new SVLexer();
		fLexer.init(this, new StringTextScanner(context.fRoot));
		fParsers = new SVParsers(this);
	}

	public SVLexer lexer() {
		return fLexer;
	}

	public void error(String msg) throws SVParseException {
		// TODO Auto-generated method stub

	}

	public void error(SVParseException e) throws SVParseException {
		// TODO Auto-generated method stub

	}

	public void warning(String msg, int lineno) {
		// TODO Auto-generated method stub

	}

	public boolean error_limit_reached() {
		// TODO Auto-generated method stub
		return false;
	}

	public SVParsers parsers() {
		return fParsers;
	}

	public void debug(String msg, Exception e) {
		// TODO Auto-generated method stub

	}

}
