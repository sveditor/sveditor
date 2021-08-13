/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.expr_utils;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.ISVParser;
import org.eclipse.hdt.sveditor.core.parser.SVLexer;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.hdt.sveditor.core.parser.SVParsers;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

public class SVExprUtilsParser implements ISVParser {
	private SVLexer			fLexer;
	private SVParsers		fParsers;
	private LogHandle		fLog;
	
	public SVExprUtilsParser(SVExprContext context) {
		this(context, false);
	}
	
	public SVExprUtilsParser(SVExprContext context, boolean parse_full) {
		fLog = LogFactory.getLogHandle("SVExprUtilsParser", ILogHandle.LOG_CAT_PARSER);
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
		fParsers.init(this);
	}
	
	public SVExprUtilsParser(String content) {
		fLog = LogFactory.getLogHandle("SVExprUtilsParser", ILogHandle.LOG_CAT_PARSER);
		fLexer = new SVLexer();
		fLexer.init(this, new StringTextScanner(content));
		fParsers = new SVParsers(this);
		fParsers.init(this);
	}

	public SVLexer lexer() {
		return fLexer;
	}
	
	public ILogHandle getLogHandle() {
		return fLog;
	}
	
	public void disableErrors(boolean dis) {
		
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
	
	public SVParserConfig getConfig() {
		return SVCorePlugin.getDefault().getParserConfig();
	}

	public void debug(String msg, Exception e) {
		// TODO Auto-generated method stub

	}

	public String getFilename(long loc) {
		return "UNKNOWN: " + loc;
	}

	
	public void enter_type_scope(ISVDBItemBase item) {
		// TBD
	}
	
	public void leave_type_scope(ISVDBItemBase item) {
		// TBD
	}
}
