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

public class SVLocation {
	private int						fLineno;
	private int						fLinepos;
	
	public SVLocation(int lineno, int linepos) {
		fLineno  = lineno;
		fLinepos = linepos;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public int getLinepos() {
		return fLinepos;
	}

}
