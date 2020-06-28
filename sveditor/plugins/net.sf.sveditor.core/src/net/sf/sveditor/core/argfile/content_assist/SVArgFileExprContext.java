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


package net.sf.sveditor.core.argfile.content_assist;

public class SVArgFileExprContext {
	public enum ArgFileContextType {
		String,
		Untriggered,
		Triggered,
		Import,
		Extends
	};
	
	// Document offset where 'leaf' begins
	public int 						fStart;
	
	public ArgFileContextType		fType;
	
	// Root of the expression
	public String					fRoot;
	
	// Leaf of the expression 
	public String					fLeaf;
	
	// Trigger character
	public String					fTrigger;

}
