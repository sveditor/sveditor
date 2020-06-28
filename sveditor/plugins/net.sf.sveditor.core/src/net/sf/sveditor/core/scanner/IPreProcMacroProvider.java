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

import net.sf.sveditor.core.db.SVDBMacroDef;

public interface IPreProcMacroProvider {
	
	SVDBMacroDef findMacro(String name, int lineno);
	
	void addMacro(SVDBMacroDef macro);
	
	void setMacro(String key, String value);

}
