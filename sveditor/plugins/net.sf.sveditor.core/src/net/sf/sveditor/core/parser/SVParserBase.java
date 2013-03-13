/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;



public class SVParserBase implements ISVParser, ILogLevelListener {
	
	protected boolean			fDebugEn = false;
	protected ISVParser			fParser;
	protected SVLexer			fLexer;
	protected SVParsers			fParsers;
	
	protected SVParserBase(ISVParser parser) {
		fParser = parser;
		fLexer = parser.lexer();
		fParsers = parser.parsers();
		
		fDebugEn = getLogHandle().isEnabled();
		getLogHandle().addLogLevelListener(this);
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = getLogHandle().isEnabled();
	}
	
	public ILogHandle getLogHandle() {
		return fParser.getLogHandle();
	}
	
	public boolean error_limit_reached() {
		return fParser.error_limit_reached();
	}
	
	public void disableErrors(boolean dis) {
		fParser.disableErrors(dis);
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
	
	protected SVDBIdentifierExpr readId() throws SVParseException {
		return fParsers.exprParser().idExpr();
	}

	public void warning(String msg, int lineno) {
		fParser.warning(msg, lineno);
	}
	
	public SVParsers parsers() {
		return fParser.parsers();
	}
	
	public SVDBLocation getLocation() {
		return fLexer.getStartLocation();
	}

	public void debug(String msg) {
		fParser.debug(msg, null);
	}

	public void debug(String msg, Exception e) {
		fParser.debug(msg, e);
	}
	
	public SVParserConfig getConfig() {
		return fParser.getConfig();
	}

	protected void setStartLocation(SVDBItem item) {
		item.setLocation(getLocation());
	}
	
	protected void setEndLocation(SVDBScopeItem item) {
		item.setEndLocation(getLocation());
	}
}
