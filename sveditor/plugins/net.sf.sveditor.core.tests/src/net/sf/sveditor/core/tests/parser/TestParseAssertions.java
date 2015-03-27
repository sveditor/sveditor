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
import net.sf.sveditor.core.parser.SVParseException;

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
		SVCorePlugin.getDefault().enableDebug(false);
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
	
	public void testPropertyParenSeq() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc =
			"module top ();\n" +
			"	parameter PARAM = 1;\n" +
			"	ap_property: assert property (\n" +
			"	@(posedge clk)\n" +
			"	($rose (restart) ##1 @ (some_sig == 1'b0)) |=> (interrupt[(PARAM-1):0] == 1'b1)\n" +
			"	);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top"});
	}
	
	public void testPropertyRepetitionSuffix() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module top ();\n" +
			"	ap_property: assert property (\n" +
			"	@(posedge clk)\n" +
			"	($rose (restart) ##1 @ (some_sig == 1'b0)) |=> (interrupt == 1'b0)[*4]\n" +
			"	);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top"});
	}

	public void testPropertyParenExpr() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module top ();\n" +
			"	property somep_property;\n" +
			"		@(posedge clk) disable iff (rst)\n" +
			"			a\n" +
			"			|-> \n" +
			"			(a) [*0:$] !b;    // Braces around 'a' cause parser error\n" +
			"	endproperty\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top"});
	}
	
	public void testPropertyParenArrayIndex() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module top ();\n" +
			"	logic clk, signala, signalb;\n" +
			"	property some_prop (addr,exp_val);\n" +
			"	@(negedge clk)\n" +
			"	signala |=> (signala[(5)] == 1'b1) \n" +
			"		##1 signalb;\n" +
			"	endproperty:  some_prop\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top"});
	}

	public void testPropertyIfStmt() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"	module AssertionErrors (\n" +
			"		input wire clk,\n" +
			"		input wire reset_n,\n" +
			"		input wire a,\n" +
			"		input wire b,\n" +
			"		input wire c,\n" +
			"		input wire d\n" +
			"	);\n" +
			"\n" +
			"	property p_example_1;\n" +
			"		@(posedge clk) disable iff (!reset_n)\n" +
			"		$fell(a) |-> \n" +
			"		if (b)\n" +
			"			##[0:7] c\n" +
			"		else\n" +
			"			##[0:15] d;\n" +
			"	endproperty\n" +
			"\n" +
			"	a_example_1: assert property(p_example_1);\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"AssertionErrors"});
	}
	

			
	
	public void testPropertyCaseStmt() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
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
	
	public void testPropertyFirstMatch() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module test ();\n" +
			"  property some_prop;\n" +
			"		@(posedge clk)\n" +
			"			(sig1 && (bus1[15:0]==SOME_PARAM) && \n" +
			"			(|be) && (bus2[14]==1'b1)) ##1\n" +
			"			first_match	(##[1:2] $fell(sig1)) |=>@(posedge sig1) (sig2 == bus3[14]) ; \n" +
			"  endproperty\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test"});
	}	

	public void testPropertyZDelay() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module top ();\n" +
			"	logic clk, signala, signalb;\n" +
			"	property some_prop (addr,exp_val);\n" +
			"		@(negedge clk)\n" +
			"			signala |=> (signala == 1'b1) \n" +
			"			##0 (signalb);\n" +
			"	endproperty:some_prop\n" +
			"endmodule\n" 
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"top"});
	}
	
	public void testPropertyWithin() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module test ();\n" +
			"property some_prop (prop_param);\n" +
			"	@(posedge clk)\n" +
			"		((bus1[prop_param] == 2'b01) && bus2[prop_param] && $rose(bus3[prop_param]) ##[0:2] bus4[prop_param] && $rose(bus5[prop_param]))\n" +
			"		within (!bus6[prop_param]);\n" +
			"endproperty\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test"});
	}
	
	
	public void testPropertyComplex() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
        " module test ();\n" +
        " property some_prop(clk, rst_n, valid, mode, timing); \n" +
        "  	    int count; \n" +
        "  	  @(posedge clk) disable iff (!rst_n || !valid) \n" +
        "	    (sigX === {sigA{1'b1}}) ##1 (sigY == mode) ##0 (1, count = timing) |=> \n" +
        "	            ($stable(sigZ) && count, count = count - 1)[*0:$] ##1 (count == 0) ##0 (sigZ === {sigB{1'b1}}); \n" +
        " endproperty\n" +
        " endmodule\n"
		;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test"});
	}
	
	public void testPropertyNot() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = getName();
		String doc =
			"module t;\n" +
			"    // dend should never unknown.\n" +
			"	ERROR_DEND_IS_UNKNOWN : assert property (disable iff ( !checks_enabled || rst || $isunknown(rst) || before_reset) ds |-> (not $isunknown(dend)));\n" +
			"\n" +
			"// data should never unknown.\n" +
			"	ERROR_DATA_IS_UNKNOWN : assert property (disable iff ( !checks_enabled || rst || $isunknown(rst) || before_reset) ds |-> (not $isunknown(data)));\n" +
			"\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"t"});
	}
	
	/**
	 * Generic testcase we can dump bug reports into
	 * @throws SVParseException
	 */
	public void testBugList() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = getName();
		String doc =
				"module t;\n" +
				"	// Bug #358 Nested brackets, in property returns \"null property\"\n" +
				"	property some_prop ();\n" +
				"		@(posedge clk)\n" +
				"			$rose(write) |-> ((mode == 1'b1));\n" +
				"	endproperty:some_prop\n" +
				"endmodule\n"
						;
		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"t"});
	}
	
	public void testPastExpression() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module top;\n" +
			"	always @*\n" +
			"	begin\n" +
			"		if ($past(reset,1,,@(posedge i_tmr_clk))) begin\n" +
			"			thing <= 1'b0;\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top" });
	}
	
	public void testGotoRepetition() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"program test;\n" +
			"	logic clk;\n" +
			"	sequence s_error;\n" +
			"	@(posedge clk)\n" +
			"		( ( (!a || $rose(a)) && $fell(b) ))\n" +
			"		##0 ( (!a || $rose(a)) &&\n" +
			"			$fell(b) ) [->1];\n" +
			"	endsequence\n" +
			"endprogram\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "test" });
	}
}
