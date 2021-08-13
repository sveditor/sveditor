/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.parser;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBScopeItem;
import org.sveditor.core.db.expr.SVDBIdentifierExpr;
import org.sveditor.core.log.ILogHandle;
import org.sveditor.core.log.ILogLevelListener;



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
	
	public long getLocation() {
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

	public String getFilename(long loc) {
		return fParser.getFilename(loc);
	}

	@Override
	public void enter_type_scope(ISVDBItemBase item) {
		fParser.enter_type_scope(item);
	}

	@Override
	public void leave_type_scope(ISVDBItemBase item) {
		fParser.leave_type_scope(item);
	}
	
}
