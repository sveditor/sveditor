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
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParseInterfaceBodyItems extends TestCase {
	
	public void testModportBasic() throws SVParseException {
		String doc = 
			"interface foo;\n" +
			"   modport foo_m(input a, b, c, output d, e, f);\n" +
			"endinterface\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testModportBasic");
		SVDBTestUtils.assertFileHasElements(file, "foo");
	}

	public void testModportMethod() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
			"interface foo;\n" +
			"   modport foo_m(\n" +
			"		import function int get(ref int a, int b),\n" +
			"		input a, b, c, output d, e, f\n" +
			"		);\n" +
			"endinterface\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testModportBasic");
		SVDBTestUtils.assertFileHasElements(file, "foo");
	}
	
// TODO: This should pass, it is passing in a normal verilog file...	
	public void testInterfaceWithParam() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
			"interface pb_if (input pb_clk, input logic inst=1'b1);\n" +
			"   timeunit 1ns;\n" +
			"   timeprecision 1ps;\n" +
			"endinterface\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testModportBasic");
		SVDBTestUtils.assertFileHasElements(file, "pb_if");
	}
	
	public void testInterfaceModportTypeField() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testInterfaceModportTypeField";
		String content =
			"interface ifa;\n" +
			"	logic a;\n" +
			"	modport slave(\n" +
			"		input a\n" +
			"	);\n" +
			"endinterface\n" +
			"\n" +
			"class myclass;\n" +
			"	virtual interface ifa.slave iface;\n" +
			"\n" +
			"	function void assign_vi (virtual interface ifa.slave a);\n" +
			"		iface=a;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, content, new String[] {"ifa", "myclass"});
	}
	
	public void testTypeParameters() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testTypeParameters";
		String content = 
			"interface some_interface #(\n" +
			"parameter type T = int, // ERROR: 'type' expression unsupported\n" +
			"parameter int BOUND = 1\n" +
			");\n" +
			"endinterface"
			;
		ParserTests.runTestStrDoc(testname, content, new String[] {"some_interface"});
	}
	
}

