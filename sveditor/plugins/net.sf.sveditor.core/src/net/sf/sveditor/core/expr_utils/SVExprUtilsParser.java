/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.expr_utils;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ISVParser;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.parser.SVParsers;
import net.sf.sveditor.core.scanutils.StringTextScanner;

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

	public String getFilename(SVDBLocation loc) {
		return "UNKNOWN: " + loc.getFileId();
	}

}
