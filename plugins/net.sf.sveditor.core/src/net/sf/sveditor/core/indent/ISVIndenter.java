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


package net.sf.sveditor.core.indent;

public interface ISVIndenter {
	
	void init(ISVIndentScanner scanner);
	
	String indent();
	
	String indent(int start, int end);
	
	String getLineIndent(int lineno);
	
	void setAdaptiveIndent(boolean en);
	
	void setAdaptiveIndentEnd(int lineno);
	
	/**
	 * Enables testing mode, where internal errors throw
	 * a runtime exception
	 * 
	 * @param tm
	 */
	void setTestMode(boolean tm);
	
}
