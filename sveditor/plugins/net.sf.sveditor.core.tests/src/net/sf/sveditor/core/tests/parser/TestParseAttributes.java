/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException; 
import junit.framework.TestCase;

public class TestParseAttributes extends TestCase {
	
	public void testPortAttribute() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module test (\n" +
			"	input clk_i,\n" +
			"	(* mark_debug = \"true\" *) input rst_n\n" +
			");\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"test"});
	}
	
}
