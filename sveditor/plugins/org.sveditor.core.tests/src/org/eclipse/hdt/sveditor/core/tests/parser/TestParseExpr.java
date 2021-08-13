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


package org.eclipse.hdt.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParseExpr extends TestCase {

	public void testTimeUnits() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		time t_s = 0.5s;\n" +
			"		time t_ms = 0.5ms;\n" +
			"		time t_us = 0.5us;\n" +
			"		time t_ns = 0.5ns;\n" +
			"		time t_ps = 0.5ps;\n" +
			"		time t_fs = 0.5fs;\n" +
			"		time t_1s = 1s;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", "t_s", "t_ms", "t_us",
					"t_ns", "t_ps", "t_fs", "t_1s"});
	}

	public void testStreamOperators() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		int a, b, c;\n" +
			"		logic [10:0] up [3:0];\n" +
			"		logic [11:1] p1, p2, p3, p4;\n" +
			"		bit [96:1] y = {>>{ a, b, c }}; // OK: pack a, b, c\n" +
			"		int j = {>>{ a, b, c }}; // error: j is 32 bits < 96 bits\n" +
			"		bit [99:0] d = {>>{ a, b, c }}; // OK: b is padded with 4 bits\n" +
			"		{>>{ a, b, c }} = 23'b1; // error: too few bits in stream\n" +
			"		{>>{ a, b, c }} = 96'b1; // OK: unpack a = 0, b = 0, c = 1\n" +
			"		{>>{ a, b, c }} = 100'b1; // OK: unpack as above (4 bits unread)\n" +
			"		{ >> {p1, p2, p3, p4}} = up; // OK: unpack p1 = up[3], p2 = up[2],\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", 
					"a", "b", "c", "up", "p1", "y"});
	}

	public void testStreamOperators2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		int variable_a, variable_b;\n" +
			"		variable_b = { << 8 { variable_a }}; //swap byte order\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", "variable_a", "variable_b"});
	}
	
	public void testStreamOperators3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +														// 1
			"function my_func;\n" +						
			"	send: begin // Create random packet and transmit\n" +
			"		byte q[$];\n" +
			"		Packet p = new;\n" +												// 5
			"		void'(p.randomize());\n" +
			"		q = {<< byte{p.header, p.len, p.payload, p.crc}}; // pack\n" +
			"		stream = {stream, q}; // append to stream\n" +
			"	end\n" +
			"\n" +																		// 10
			"	receive: begin // Receive packet, unpack, and remove\n" +
			"		byte q[$];\n" +
			"		Packet p = new;\n" +
			"		{<< byte{ p.header, p.len, p.payload with [0 +: p.len], p.crc }} = stream;\n" +
			"		stream = stream[ $bits(p) / 8 : $ ]; // remove packet\n" +
			"	end\n" +
			"endfunction\n" +
			"endclass\n"
			;
		runTest("testStreamOperators3", content,
				new String[] {"my_class", "my_func"});
	}

	public void testAssociativeArrayFieldInit() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"	static my_enum field[my_id_t] = {KEY : VAL};\n" +
			"endclass\n"
			;
		runTest(getName(), content,
				new String[] {"my_class"});
	}

	public void testAssociativeArrayFieldInit2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"	static my_enum field[my_id_t] = {KEY1 : VAL1, KEY2 : VAL2, KEY3 : VAL3};\n" +
			"endclass\n"
			;
		runTest(getName(), content,
				new String[] {"my_class"});
	}
	
	public void testStringEmbeddedBackslashes() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"\n" +
			"	function do_something;\n" +
			"		if (my_string == \"\\\\\")\n" +
			"			$display(\"Hello World\");\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testStringEmbeddedBackslashes", content,
				new String[] {"my_class", "do_something"});
	}

	public void testStringEmbeddedComment() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"\n" +
			"	function do_something;\n" +
			"		if (my_string == \"\\\\\")\n" +
			"			$display(\"Hello World // this is a comment\");\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testStringEmbeddedComment", content,
				new String[] {"my_class", "do_something"});
	}
	
	public void testTFCallWithUnspecifiedParams() throws SVParseException {
		String testname = "testTFCallWithUnspecifiedParams";
		String content = 
			"module m;\n" +
			"\n" +
			"task ommitted_param2(int a, int b=0);\n" +
			"endtask\n" +
			"\n" +
			"task ommitted_param3(int a, int b=0,int c=1);\n" +
			"endtask\n" +
			"\n" +
			"initial begin\n" +
			"	ommitted_param2(1,);\n" +
			"	ommitted_param3(1,,3);\n" +
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		runTest(testname, content,
				new String[] {"m", "ommitted_param2", "ommitted_param3"});
	}
	
	public void testDelayExpressionTrailingAND() throws SVParseException {
		String testname = "testDelayExpressionTrailingAND";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module m;\n" +
			"	initial begin\n" +
			"		if(DetectionWindow & ByteCntEq1)\n" +    
			"			AddressOK <= #Tp (RxData[7:0] == ReservedMulticast[39:32] | RxData[7:0] == MAC[39:32]) & AddressOK;\n" +
			"		\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		runTest(testname, content, new String[] {"m"});
	}
	
	public void testDelayArrayRefExpr() throws SVParseException {
		String testname = "testDelayArrayRefExpr";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"	function f;\n" +
			"		time timeval[2];\n" +
			"		timeval[0] = 1ms;\n" +
			"		#timeval[0];\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "f"});
	}

	public void testWireAssignMacroExpr() throws SVParseException {
		String testname = "testWireAssignMacroExpr";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"`define ETH_MODER_ADR         8'h0    // 0x0\n" + 
			"`define ETH_INT_SOURCE_ADR    8'h1    // 0x4\n" +
			"\n" +
			"module m;\n" +
			"	wire [3:0] Write =   Cs  & {4{Rw}};\n" +
			"	wire       Read  = (|Cs) &   ~Rw;\n" +
			"	wire MODER_Sel      = (Address == `ETH_MODER_ADR       );\n" +
			"	wire INT_SOURCE_Sel = (Address == `ETH_INT_SOURCE_ADR  );\n" +
			"endmodule\n"
			;
		
		runTest(testname, content, new String[] {"m"});
	}
	
	public void testWireAssignMiscOperators () throws SVParseException {
		String testname = "testWireAssignMacroExpr";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
						"module m;\n" +
					    "  wire a, b, c;\n" +
				        "  assign c =  (a ~^ b);		// XNOR\n"+
				        "  assign c =  (a ^~ b);		// XNOR\n"+
						"endmodule\n"
						;
		
		runTest(testname, content, new String[] {"m"});
	}
	
	public void testConcatTernaryStringExpr() throws SVParseException {
		String testname = "testConcatTernaryStringExpr";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content =
			"class c;\n" +
			"	function f;\n" +
			"		string msg;\n" +
			"		msg = {msg, (i == 1) ? str1 : str2, \"str3\" };\n" +
			"		msg = {msg, (i == 1) ? \"str1\" : str2, \"str3\" };\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c"});
	}
	
	public void testAssignTLeftShift() throws SVParseException {
		String testname = "testAssignTLeftShift";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"	logic a;\n" +
			"	assign a = 1 <<< 2; // error.\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"t"});
	}

	public void testAssignTRightShift() throws SVParseException {
		String testname = "testAssignTRightShift";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"	logic a;\n" +
			"	assign a = 'h1000 >>> 2; // error.\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"t"});
	}

	public void testAssignBitSelect() throws SVParseException {
		String testname = "testAssignBitSelect";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"	struct {" +
			"		bit[3:0] a;\n" +
			"	} svar;\n" +
			"\n" +
			"	initial begin\n" +
			"		svar::a[1:0] = 1;\n" +
			"	end\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"t"});
	}

	public void testDelayControlAdjacentBasedNumber() throws SVParseException {
		String testname = "testDelayControlAdjacentBasedNumber";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"	logic a,b;\n" +
			"	always @ (posedge a) b <= #1 'b1; // error.\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"t"});
	}
	
	public void testInlineDistConstraint() throws SVParseException {
		String testname = "testInlineDistConstraint";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"	rand bit[3:0] a;\n" +
			"	rand bit[3:0] b;\n" +
			"\n" +
			"	function void foo();\n" +
			"		c v = new;\n" +
			"		assert(v.randomize() with {\n" +
			"			a dist {[0:1] := 1, [2:15] :/1};\n" +
			"			b dist {[0:1] := 1, [2:15] :/1};\n" +
			"		});\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "foo"});
	}

	public void testNewExprCall() throws SVParseException {
		String testname = "testNewExprCall";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"	rand bit[3:0] a;\n" +
			"	rand bit[3:0] b;\n" +
			"\n" +
			"	function void foo();\n" +
			"		c v = new this;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(testname, content, new String[] {"c", "foo"});
	}

	public void testVirtualInterfaceSysTFParam() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"	rand bit[3:0] a;\n" +
			"	rand bit[3:0] b;\n" +
			"\n" +
			"	function void foo();\n" +
			"		$display($typename(virtual some_interface));\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(getName(), content, new String[] {"c", "foo"});
	}
	
	public void testSignedLiterals() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module top;\n" +
			"	assign coeffs[0] = { 8'sd64, 8'sd0 , 8'sd0 , 8'sd0 , 8'sd0 , 8'sd0 , 8'sd0 , 8'sd0 };\n" +
			"	initial begin\n" +
			"		var1 <= var2 + 5'sd8;\n" +
			"	end\n" +
			"endmodule\n"
			;
		runTest(getName(), content, new String[] {"top"});
	}
	
	public void testMultiLineStrings() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module top;\n" +
			"	string str = \"\\n\n" +
			"	All their equipment and instruments are alive\n" +
			"	\";\n" +
			"endmodule\n"
			;
		runTest(getName(), content, new String[] {"top"});
	}
	
	public void testMultiLineStringMacro() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"`define DSTR(name, init)\\\n" +
			"	string name = init\n" +
			"module top;\n" +
			"	`DSTR(str, \"\\\\n\n" +
			"	All their equipment and instruments are alive\n" +
			"	\");\n" +
			"endmodule\n"
			;
		runTest(getName(), content, new String[] {"top"});
	}
	
	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		LogHandle log = LogFactory.getLogHandle(testname);
		SVDBFile file = SVDBTestUtils.parse(log, doc, testname, markers);

		for (SVDBMarker m : markers) {
			log.debug("[MARKER] " + m.getMessage());
		}
		assertEquals(0, markers.size());
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}
}
