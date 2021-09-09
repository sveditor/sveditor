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


package org.sveditor.core.tests.parser;

import org.sveditor.core.tests.SVDBTestUtils;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;

public class TestLexer extends TestCase {
	
	public void testSpaceContainingNumber() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"class c;\n" +
			"	int a = 32 'h 0000_1111_2222_3331;\n" +
			"	int b = 32'h 0000_1111_2222_3332;\n" +
			"	int d = 32'd 0000_1111;\n" +
			"	int e = 3_2'd 123;\n" +
			"endclass\n";
		
		runTest("testSpaceContainingNumber", content, new String[] {"c", "b", "d", "e"});
	}
	
	public void testParenContainingString() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"`define ovm_file `__FILE__\n" +
			"`define ovm_line `__LINE__\n" +
			"`define ovm_warning(region, msg) \\\n" +
			"   begin \\\n" +
			"		if (ovm_report_enabled(OVM_NONE,OVM_WARNING,ID)) \\\n" +
			"			ovm_report_warning (ID, MSG, OVM_NONE, `ovm_file, `ovm_line); \\\n" +
			"		end\n" +
			"\n" +
			"class c;\n" +
			"	function void test();\n" +
			"		`ovm_warning(\"WARN\", \"(\");\n" +
			"	endfunction\n" +
			"endclass\n";
		
		runTest("testParenContainingString", content, new String[] {"c", "test"});
	}
		

	public void testDefinedMacroCallWithStatement() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testDefinedMacroCallWithStatement";
		String content = 
			"`define MY_ASSERT(stmt) assert(stmt)\n" +
			"\n" +
			"class c;\n" +
			"	function void test();\n" +
			"		`MY_ASSERT(foo.randomize() with {a == 2; b < 3; c > 5;});\n" +
			"	endfunction\n" +
			"endclass\n";
		
		runTest(testname, content, new String[] {"c", "test"});
	}

	public void testEscapedIdentifier() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"module \\1ff ;\n" +
			"	reg a, b, c, d, e;\n" +
			"	reg f, g, h, i;\n" +
			"endmodule\n";
		
		runTest(getName(), content, new String[] {"1ff", "a", "b", "d", "e"});
	}
	
	public void testEscapedIdentifier_2() throws SVParseException {
		String content =
				"module tb;\n" +
				"	wire a;\n" +
				"	wire \\1w ; // <- this is ok\n" +
				"	wire [1:0]\\2w ; // <- shows syntax error\n" +
				"	wire [2:0] \\3w ; // <- shows syntax error\n" +
				"	assign a = \\1w ; // <- shows syntax error\n" +
				"\n" +
				"	pullup r1 (\\1w ); // <- shows syntax error\n" + 
				"endmodule\n";
	
		SVCorePlugin.getDefault().enableDebug(false);
		runTest(getName(), content, new String[] {
			"1w", "2w", "3w"});
				
	}

	public void EXP_FAIL_testUnDefinedMacroCallWithStatement() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testDefinedMacroCallWithStatement";
		String content = 
			"class c;\n" +
			"	function void test();\n" +
			"		if (a)\n" + 
			"			`MY_ASSERT(foo.randomize() with {a inside {[2:3]};})\n" +
			"		else\n" +
			"			`MY_ASSERT(foo.randomize() with {a inside {[2:3]};})\n" +
			"	endfunction\n" +
			"endclass\n";
		
		runTest(testname, content, new String[] {"c", "test"});
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		SVDBFile file = SVDBTestUtils.parse(log, doc, testname, false);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
	
}
