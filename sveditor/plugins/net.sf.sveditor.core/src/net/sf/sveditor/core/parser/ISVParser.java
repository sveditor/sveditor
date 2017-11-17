/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.log.ILogHandle;



public interface ISVParser extends ISVKeywords, ISVOperators {
	
	SVLexer lexer();
	
	// ITextScanner scanner();
	
	void error(String msg) throws SVParseException;

	void error(SVParseException e) throws SVParseException;
	
	void warning(String msg, int lineno);
	
	boolean error_limit_reached();
	
	void disableErrors(boolean dis);
	
	SVParsers parsers();
	
	void debug(String msg, Exception e);
	
	ILogHandle getLogHandle();
	
	SVParserConfig getConfig();
	
	String getFilename(long loc);

	/**
	void enter_type_scope(ISVDBItemBase item);
	
	void leave_type_scope(ISVDBItemBase item);
	 **/
	
}
