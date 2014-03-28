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

public class SVParseException extends Exception {
	
//	private String						fMessage;
	private String						fFilename;
	private int							fLineno;
	private int							fLinepos;
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private SVParseException(String msg, String filename, int lineno, int linepos) {
//		super(msg);
		super(filename + ":" + lineno + " " + msg);
//		fMessage  = msg;
		fFilename = filename;
		fLineno = lineno;
		fLinepos = linepos;
	}
	
	public String getFilename() {
		return fFilename;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public int getLinepos() {
		return fLinepos;
	}
	
	public static SVParseException createParseException(String msg, String filename, int lineno, int linepos) {
		return new SVParseException(msg, filename, lineno, linepos);
	}
}
