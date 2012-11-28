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

public class TestParseBehavioralStmts extends TestCase {

	public void testModulePreBodyImport3() {
		String doc = 
			"package p;\n" +
			"endpackage\n" +
			"\n" +
			"module t import p::*, p1::*, p2::*;\n" +
			"	#(\n" +
			"		parameter a = 0\n" +
			"	) // Error.\n" +
			"	();\n" +
			"endmodule\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testModulePreBodyImport3", doc, new String[] {
				"p", "t", "p::*", "p1::*", "p2::*"});
	}

	public void testVarDeclForStmt() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		for (int i=0; i<5; i++) begin\n" +
			"			x++;\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVarDeclForStmt", doc, new String[] { "t" });
		
	}
	
	public void testMultiVarDeclForStmt() throws SVParseException {
		String doc = 
			"module a;\n" +
			"	initial\n" + 
			"		for(int i=0, long j=5;\n" +
			"			i<10, j<20;\n" +
			"			i++, j++)\n" +
			"			$display(\"asdf\");\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVarDeclForStmt", doc, new String[] { "a" });
	}

	public void testNonBlockingEventTrigger() throws SVParseException {
		String doc =
			"module t;\n" +
			"	event event_identifier;\n" +
			"	initial begin\n" +
			"		->> event_identifier;\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testNonBlockingEventTrigger", doc, new String[] { "t" });
		
	}

	public void testEventDelayedNonBlockingAssign() throws SVParseException {
		String doc =
			"module t;\n" +
			"	bit clk;\n" +
			"	int a;\n" +
			"	initial begin\n" +
			"		a <= @(posedge clk) 1;\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testNonBlockingEventTrigger", doc, new String[] { "t" });
		
	}

	public void testVirtualInterfaceParameterizedStaticCall() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		class_type_name #(virtual interface_type_name)::static_class_method();\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVirtualInterfaceParameterizedStaticCall", doc, new String[] { "t" });
	}

	public void testConstIntParameterizedStaticCall() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		class_type_name #(const int)::static_class_method();\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testConstIntParameterizedStaticCall", doc, new String[] { "t" });
	}
		
	public void testStringParameterizedStaticCall() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		class_type_name #(string)::static_class_method();\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testStringParameterizedStaticCall", doc, new String[] { "t" });
	}
	
	public void testEmptyParameterizedStaticCall() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		class_type_name #()::empty_static_class_method();\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testEmptyParameterizedStaticCall", doc, new String[] { "t" });
	}
	
	public void testVarDeclListForStmt() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		for (int i=0, j=2; i<5; i++, j++) begin\n" +
			"			x++;\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVarDeclListForStmt", doc, new String[] { "t" });
		
	}
	
	
	public void testVarDeclListForStmt2() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"	for(i__=0; i__<data.size() && i__<local_data__.data.size(); ++i__) begin\n" +
			"			x++;\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVarDeclListForStmt", doc, new String[] { "t" });
		
	}

	public void testOmittedTFCallParams() throws SVParseException {
		String doc =
			"class c;\n" +
			"	function void foo(string A, int B=1, string C=2, int D=3);\n" +
			"	endfunction\n" +
			"\n" +
			"	function bar();\n" +
			"		foo(\"FOO\" ,,\"BAR\",4);\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testVarDeclListForStmt", doc, 
				new String[] { "c", "foo", "bar" });
	}
	
	public void testAssertBodyTFDottedArgs() {
		String testname = "testAssertBodyTFDottedArgs";
		String doc = 
				"module m;\n" +
				"function bit test_assert(int arg1, int arg2);\n" +
				" return 0;\n" +
				" endfunction\n" +
				"\n" +
				" initial begin\n" +
				" assert(test_assert(0, 1)); //ok\n" +
				" assert(test_assert(0, .arg2(1))); // not ok -- unexpected .\n" +
				" end\n" +
				"endmodule\n"
				;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(testname, doc, 
				new String[] { "m", "test_assert"});
	}
	
	public void testListFindWith() {
		String testname = "testListFindWith";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"class m;\n" +
			"	function bit check_for_element(ref uint member_list[$], uint queue_no);\n" +
			"		uint temp_q_list[$];\n" +
			"		temp_q_list = member_list.find(x) with (x == queue_no); // <- expecting an identifier or keyword; found ‘=’\n" +
			"		if (temp_q_list.size())\n" +
			"		begin\n" +
			"			return (1'b1);\n" +
			"		end\n" +
			"		else\n" +
			"		begin\n" +
			"			return (1'b0);\n" +
			"		end\n" +
			"	endfunction: check_for_element\n" +
			"endclass\n" 
  			;
		
		runTest(testname, doc, 
				new String[] { "m"});
	}

	public void testListFindWith_2() {
		String testname = "testListFindWith_2";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"	function bit check_for_element(ref uint member_list[$], uint queue_no);\n" +
			"		uint temp_q_list[$];\n" +
			"		temp_q_list = member_list.find(x) with (x == queue_no); // <- expecting an identifier or keyword; found ‘=’\n" +
			"		if (temp_q_list.size())\n" +
			"		begin\n" +
			"			return (1'b1);\n" +
			"		end\n" +
			"		else\n" +
			"		begin\n" +
			"			return (1'b0);\n" +
			"		end\n" +
			"	endfunction: check_for_element\n"
			;
		
		runTest(testname, doc, 
				new String[] { "check_for_element"});
	}

	public void testListUnique() {
		String testname = "testListUnique";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc =
			"class c;\n" +
			"	rand bit [4:0] q_number[];\n" +
			"	bit [4:0] temp_q_list[$];\n" +
			"\n" +
			"	function f;\n" +
			"		temp_q_list = q_number.unique(); // <- expecting one of keyword ‘endfunction’ received ‘unique’.\n" +
			"	endfunction\n" +
			"endclass\n" 
			;
		
		runTest(testname, doc, 
				new String[] { "c", "f"});
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
