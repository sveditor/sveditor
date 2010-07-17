package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBScopeItem;



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
	
	public void error(String msg) throws SVParseException {
		fParser.error(msg);
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
	
	public SVDBLocation getLocation() {
		return fParser.lexer().getStartLocation();
	}

	public void debug(String msg) {
		fParser.debug(msg);
	}

	protected void setStartLocation(SVDBItem item) {
		item.setLocation(getLocation());
	}
	
	protected void setEndLocation(SVDBScopeItem item) {
		item.setEndLocation(getLocation());
	}
}
