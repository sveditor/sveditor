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

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;

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
	
	public void testContinueAsVarName() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"       reg continue = 1;\n" + // MSB: change from 'bit' continue
			"       reg thing = 0 ;\n" +
			"		while (continue) begin\n" +
			"			thing++ ;\n" +
			"           if(thing > 10)\n" +
			"                continue = 0 ;\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(SVLanguageLevel.Verilog2005, getName(),
				doc, new String[] { "t" });
		
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

	public void testCaseNonBody() throws SVParseException {
		String doc = 
			"class c;\n" +
			"	function f;\n" +
			"		begin\n" +
			"			case (frame_type)\n" +
			"				TXDMA_CHAIN_BDE:\n" +
			"					case (word_counter)\n" +
			"						0:  begin\n" +
			"						end\n" +
			"						1:  begin\n" +
			"						end\n" +
			"						default:\n" +
			"						begin\n" +
			"						end\n" +
			"					endcase\n" +
			"				TXDMA_CHAIN_INL:\n" +
			"				TXDMA_CHAIN_CMP:\n" +
			"				TXDMA_CHAIN_NO:\n" +
			"				//  begin\n" +
			"				//  end\n" +
			"			endcase\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n"
			;
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(getName(), doc, new String[] { "c", "f" });
	}

	public void testCaseNonBlockingDelayAssign() throws SVParseException {
		String doc = 
			"class c;\n" +
			"	function f;\n" +
			"		begin\n" +
			"			case (frame_type)\n" +
			"				1: a <= #1 25;\n" +
			"				2:\n" +
			"				3:\n" +
			"			endcase\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n" 
			;
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(getName(), doc, new String[] { "c", "f" });
	}

	public void testCaseRangeCaseItem() throws SVParseException {
		String doc = 
			"class c;\n" +
			"	function f;\n" +
			"		begin\n" +
			"			case (frame_type) inside\n" +
			"				1: a <= #1 25;\n" +
			"				[2:3]: a <= #1 35;\n" +
			"			endcase\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n" 
			;
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(getName(), doc, new String[] { "c", "f" });
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
	
	public void testBasicDelay() throws SVParseException {
		String doc =
			"module t;\n" +
			"	initial begin\n" +
			"		#10 ;\n" +
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testBasicDelay", doc, new String[] { "t" });
		
	}
	
	public void testDelayFromClassMember() throws SVParseException {
		String doc =
			"class cfg;\n" +
		    "   int dly;" +
			"endclass\n" +
			"class t;\n" +
			"   cfg c;" +
			"	task sometask();\n" +
			"       for (int i = 0 ; i < 8 ; i++) begin" +
			"			#this.c.dly ;\n" +
			"       end" +
			"	endtask\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testDelayFormClassMember", doc, new String[] { "t" });
		
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
	
	public void testAssertSingleStmt() {
		String doc = 
				"module m;\n" +
				"function bit test_assert(int arg1, int arg2);\n" +
				" return 0;\n" +
				" endfunction\n" +
				"\n" +
				" initial begin\n" +
				" assert(test_assert(0, 1)) $display(\"Assert failed\");\n" + 
				" assert(test_assert(0, .arg2(1)));\n" +
				" end\n" +
				"endmodule\n"
				;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(getName(), doc, 
				new String[] { "m", "test_assert"});
	}
	
	public void testListFindWith() {
		String testname = "testListFindWith";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class m;\n" +
			"	function bit check_for_element(ref uint member_list[$], uint queue_no);\n" +
			"		uint temp_q_list[$];\n" +
			"		temp_q_list = member_list.find(x) with (x == queue_no); // <- expecting an identifier or keyword; found ���=���\n" +
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
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"	function bit check_for_element(ref uint member_list[$], uint queue_no);\n" +
			"		uint temp_q_list[$];\n" +
			"		temp_q_list = member_list.find(x) with (x == queue_no); // <- expecting an identifier or keyword; found ���=���\n" +
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
	
	public void testArrayReduction() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module test;\n" +
			"	initial begin\n" +
			"		begin\n" +
 			"			automatic byte b[] = { 1, 2, 3, 4 };\n" +
 			"			int y;\n" +
 			"			y = b.sum ; // y becomes 10 => 1 + 2 + 3 + 4\n" +
 			"			y = b.product ; // y becomes 24 => 1 * 2 * 3 * 4\n" +
 			"			y = b.xor with ( item + 4 ); // y becomes 12 => 5 ^ 6 ^ 7 ^ 8\n" +
 			"			y = b.and();\n" +
 			"			y = b.or();\n" +
 			"		end\n" +
 			"		begin\n" +
 			"			automatic logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };\n" +
 			"			int y;\n" +
 			"			y = m.sum with (item.sum() with (item)); // y becomes 50 => 5+10+15+20\n" +
 			"		end\n" +
 			"		begin\n" +
 			"			logic bit_arr [1024];\n" +
 			"			int y;\n" +
 			"			y = bit_arr.sum with ( int'(item) ); // forces result to be 32-bit\n" +
 			"		end\n" +
 			"	end\n" +
 			"endmodule\n"
 			;
		runTest(getName(), doc, new String[] { "test"});
	}

	public void testListUnique() {
		String testname = "testListUnique";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class c;\n" +
			"	rand bit [4:0] q_number[];\n" +
			"	bit [4:0] temp_q_list[$];\n" +
			"\n" +
			"	function f;\n" +
			"		temp_q_list = q_number.unique(); // <- expecting one of keyword ���endfunction��� received ���unique���.\n" +
			"	endfunction\n" +
			"endclass\n" 
			;
		
		runTest(testname, doc, 
				new String[] { "c", "f"});
	}
	
	public void testRandomizeWithInMacro() {
		// This test ends up verifying that the '(' for a macro
		// with arguments can be separated by any amount of
		// whitespace
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define msg_fatal(msg)\n" +
			"`define randcheck(arg) begin\\\n" +
			" bit pass_fail; \\\n" +
			" pass_fail = (arg); \\\n" +
			" if (pass_fail === 0) `msg_fatal((`\"arg failed to randomize`\")); \\\n" +
			" end\n" +
			"\n" +
			"class c;\n" +
			"	function f;\n" +
			"		for (int iocb_count = 0; iocb_count < iocb_this_hqp; iocb_count++)\n" +
            "       begin\n" +
            "       qs_iocb_c               test_iocb;          ///< IOCB\n" +
            "       test_iocb = test_hqp.append_iocb();\n" +
            "       `randcheck\n" +
            "           (\n" +
            "           test_iocb.randomize() with\n" +
            "               {\n" +
            "               iocb_tx_opcode == TXDMA_OPCODE_1_FCOE;\n" +
            "               iocb_tx_enable_t10 == 0;\n" +
            "               iocb_tx_queue inside {[MIN_QUEUE:MAX_QUEUE]};\n" +
            "               iocb_tx_chain_count == 1;\n" +
            "               }\n" +
            "           )\n" +
            "       if (1)\n" +
            "           begin\n" +
            "           test_iocb.print();\n" +
            "           end\n" +
            "        end\n" + // end forloop
			"    endfunction\n" +
            "endclass\n"
			;
		
		runTest(getName(), doc, new String[] {"c", "f"});
	}

	public void testDefineAmbiguousTimeUnit() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define DLY 0.25\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		pre <= #`DLY pre_next;\n" +
			"	end\n" +
			"endmodule\n"
			;

		runTest(getName(), doc, new String[] {"top"});
	}

	public void testAssertWithBlockBodyStmt() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
				"`define RPT_GET_FUNC_NAME(mesid) \\\n" +
				"  begin\\\n" +
				"    int i;\\\n" +
				"    $sformat(mesid, \"%m\");\\\n" +
				"    for (i=(mesid.len()-1); i > 0; i--)\\\n" +
				"       if (mesid[i] == \".\") break;\\\n" +
				"    if (i > 0)\\\n" +
				"       mesid = mesid.substr(i+1, mesid.len()-1);\\\n" +
				"    mesid = {mesid, \"()\"};\\\n" +
				"  end\n" +
				"\n" +
				"`define RPT_REPORT_MESSAGE(id,str,lev)\\\n" +
				"  begin\\\n" +
				"     string mid;\\\n" +
				"     `RPT_GET_FUNC_NAME(mid)\\\n" +
				"     ovm_report_info(id, $psprintf(\"%s: %s\", mid, str),lev);\\\n" +
				"  end\n" +
				"\n" +
				"`define RPT_MESSAGE_HIGH(id,str)  `RPT_REPORT_MESSAGE(id,str,OVM_HIGH)\n" +
				"class foobar;\n" +
				"	function void build();\n" +
				"		int myid;\n" +
				"		assert(get_config_int(\"foo_id\", myid))\n" +
				"      `RPT_MESSAGE_HIGH($psprintf(\"MSG(%s)\", this.get_full_name()), $psprintf(\"this is a message %d\", myid))\n" +
				"	endfunction\n" +
				"endclass\n" +
				"\n";
			;

		runTest(getName(), doc, new String[] {"foobar"});
	}

	public void testAmbiguousDeclarationIndexedArr() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
				"function void foo();\n" +
				"	if (bar) begin\n" +
				"		m_arr[count+:4] = 1;\n" +
				"	end\n" +
				"endfunction\n"
			;

		runTest(getName(), doc, new String[] {"foo"});
	}
	
	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		runTest(SVLanguageLevel.SystemVerilog, testname, doc, exp_items);
		
	}
	private void runTest(
			SVLanguageLevel	language,
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		SVDBFile file = SVDBTestUtils.parse(log, language, doc, testname, false);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}
	
}
