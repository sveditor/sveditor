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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;
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
