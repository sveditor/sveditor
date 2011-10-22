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

public class TestLexer extends TestCase {
	
	public void testSpaceContainingNumber() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"class c;\n" +
			"	int a = 32 'h 0000_1111_2222_3331;\n" +
			"	int b = 32'h 0000_1111_2222_3332;\n" +
			"endclass\n";
		
		runTest("testSpaceContainingNumber", content, new String[] {"c", "b"});
	}
	
	public void testParenContainingString() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
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

	public void testUnDefinedMacroCallWithStatement() throws SVParseException {
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
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}
	
}
