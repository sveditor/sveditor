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


package net.sf.sveditor.core.indent;

public interface ISVIndenter {
	
	void setIndentIncr(String incr);
	
	void init(ISVIndentScanner scanner);
	
	String indent();
	
	/**
	 * Indent and return a portion of the file, between start and end.  
	 * Us this with setAdaptiveIndentEnd which will determine the reference
	 * leading whitespace.
	 * 
	 * If you set the "setAdaptiveIndentEnd(10)" to early in the file, the
	 * indenter will use that point as a reference and continue on through the file
	 * 
	 * Calling this function with arguments 15 to 20, will have the indent on line 15
	 * be the "modified indent" for all lines between lines 10 (reference) and 15. 
	 * 
	 * Note: The first line in the file is line 1, not zero
	 * 
	 * @param start - start line (default to -1)
	 * @param end   - end line   (default to -1)
	 * @return
	 */
	String indent(int start, int end);
	
	String getLineIndent(int lineno);
	
	/**
	 * This task does nothing at the moment... comments commented out
	 * @param en
	 */
	void setAdaptiveIndent(boolean en);
	
	/**
	 * This function is used to set the line to use as the reference line for whitespace.  
	 * For example, if you are only indenting a part of the code, you'd set this to the line
	 * above the lines you are working on, and this will be used as the starting indent
	 * 
	 * NOTE: The first line in the file is '1', not '0'
	 * @param lineno - line to take subsequent indenting from, -1 by default
	 */
	void setAdaptiveIndentEnd(int lineno);
	
	/**
	 * Enables testing mode, where internal errors throw
	 * a runtime exception
	 * 
	 * @param tm
	 */
	void setTestMode(boolean tm);
	
}
