/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
