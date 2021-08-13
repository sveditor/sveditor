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


package org.sveditor.core.expr_utils;

public class SVExprContext {
	public enum ContextType {
		String,
		Untriggered,
		Triggered,
		Import,
		Extends
	};
	
	// Document offset where 'leaf' begins
	public int 						fStart;
	
	public ContextType				fType;
	
	// Root of the expression
	public String					fRoot;
	
	// Leaf of the expression 
	public String					fLeaf;
	
	// Trigger character
	public String					fTrigger;

}
