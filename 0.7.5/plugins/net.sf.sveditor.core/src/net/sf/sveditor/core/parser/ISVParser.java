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

import net.sf.sveditor.core.log.ILogHandle;



public interface ISVParser {
	
	SVLexer lexer();
	
	// ITextScanner scanner();
	
	void error(String msg) throws SVParseException;
	
	void error(SVParseException e) throws SVParseException;
	
	void warning(String msg, int lineno);
	
	boolean error_limit_reached();
	
	SVParsers parsers();
	
	void debug(String msg, Exception e);
	
	ILogHandle getLogHandle();
	
}
