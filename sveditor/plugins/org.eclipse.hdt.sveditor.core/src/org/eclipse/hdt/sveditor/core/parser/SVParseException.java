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


package org.eclipse.hdt.sveditor.core.parser;

public class SVParseException extends Exception {
	enum Kind {
		ParseError,
		AbortToTop
	}

	private Kind						fKind;
//	private String						fMessage;
	private String						fFilename;
	private int							fLineno;
	private int							fLinepos;
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private SVParseException(Kind kind) {
		fKind = kind;
		fFilename = "";
		fLineno = -1;
		fLinepos = -1;
	}

	private SVParseException(String msg, String filename, int lineno, int linepos) {
//		super(msg);
		super(filename + ":" + lineno + " " + msg);
//		fMessage  = msg;
		fKind = Kind.ParseError;
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
	
	public Kind getKind() {
		return fKind;
	}

	// Creates an exception 
	public static SVParseException createAbortToTopException() {
		return new SVParseException(Kind.AbortToTop);
	}
	
	public static SVParseException createParseException(String msg, String filename, int lineno, int linepos) {
		return new SVParseException(msg, filename, lineno, linepos);
	}
}
