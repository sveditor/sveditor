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


package net.sf.sveditor.core.scanner;


public interface IDefineProvider {
	
	String expandMacro(String string, String filename, int lineno);
	
	boolean isDefined(String name, int lineno);
	
	boolean hasParameters(String key);
	
	void addErrorListener(IPreProcErrorListener l);
	
	void removeErrorListener(IPreProcErrorListener l);
	
	// Pass an error through the DefineProvider
	void error(String msg, String filename, int lineno);

}
