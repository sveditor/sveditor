/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.tests.checker;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;

public class TestCheckMethods extends TestCase {
	
	public void testUnknownVarRef() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content = 
				"class cls;\n"							// 1
				+ "int  m_field;\n"
				+ "\n"
				+ "  function void doit();\n"
				+ "		for (i=0; i<16; i++) begin\n"	// 5
				+ "			m_field++;\n"
				+ "		end\n" 
				+ "  endfunction\n"						// 8
				+ "endclass\n"
				;
		
		CheckerTests.runTest(getName(), content,
				"5:i cannot be resolved to a variable"
				);
	}

}
