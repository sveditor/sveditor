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

public class TestParseAssertions extends TestCase {
	
	public void testOvmXbusAssertions() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testOvmXbusAssertions_repetition() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testBasicProperties() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/basic_properties.sv",
				new String[] {"my_module"});
	}

	public void testSavedValueProperty() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testSavedValueProperty",
				"/data/assertions/saved_value_property.sv",
				new String[] {"saved_value_property","p1"});
	}
	
	public void testPropertyDisableIffIf() throws SVParseException {
		String testname = "testPropertyDisableIffIf";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"module test ();\n" +
			"	property someprop;" +
			"		@(posedge clk)" +
			"		disable iff(reset)" +
			"			(somesignal ) |->" +
			"				if (signal_next == 'h1) // error on this line, unexpected if\n" +
			"				##1 (some_other_signal == 'h0 );\n" +
			"	endproperty\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test"});
	}
	
	public void testPropertyCaseStmt() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(true);
		String testname = "testPropertyCaseStmt";
		String doc =
			"module t;\n" +
			"property p_delay(logic [1:0] delay);\n" +
			"  case (delay)\n" +
			"	2'd0 : a && b;\n" +
			"   2'd1 : a ##2 b;\n" +
			"   2'd2 : a ##4 b;\n" +
			"   2'd3 : a ##8 b;\n" +
			"   default: 0; // cause a failure if delay has x or z values\n" +
			"  endcase\n" +
			"endproperty\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"t"});
	}

}
