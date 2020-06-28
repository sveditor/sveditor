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


package net.sf.sveditor.core.scanner;


public interface IDefineProvider {
	
	String expandMacro(String string, String filename, int lineno);
	
	boolean isDefined(String name, int lineno);
	
	boolean hasParameters(String key, int lineno);
	
	void addErrorListener(IPreProcErrorListener l);
	
	void removeErrorListener(IPreProcErrorListener l);
	
	// Pass an error through the DefineProvider
	void error(String msg, String filename, int lineno);

}
