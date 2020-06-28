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


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.log.ILogHandle;



public interface ISVParser extends 
	ISVKeywords, ISVOperators, ISVParserTypeListener {
	
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

}
