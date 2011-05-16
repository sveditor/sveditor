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
		this(context, false);
	}
	
	public SVExprUtilsParser(SVExprContext context, boolean parse_full) {
		StringBuilder content = new StringBuilder();
		
		if (context.fTrigger == null) {
			content.append(context.fLeaf);
		} else {
			content.append(context.fRoot);
			if (parse_full) {
				content.append(context.fTrigger);
				content.append(context.fLeaf);
			}
		}
		
		fLexer = new SVLexer();
		fLexer.init(this, new StringTextScanner(content));
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
