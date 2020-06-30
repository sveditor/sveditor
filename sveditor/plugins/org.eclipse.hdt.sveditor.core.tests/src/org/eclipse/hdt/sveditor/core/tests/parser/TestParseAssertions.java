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


package net.sf.sveditor.core.tests.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

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
				new String[] {"test", "someprop"});
	}

	public void testPropertyIffImpl_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module test ();\n" +
			"	property p_prop;\n" +
			"		@(posedge clk) 1'b1 iff (a and b or c)\n" +
			"		##1\n" +
			"		@(posedge clk) ((a and ~a) or (a or ~a))\n" +
			"		|-> (c and d or e);\n" +
			"	endproperty\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"test", "p_prop"});
	}
	
	public void testPropertyParenSeq() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
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
				new String[] {"top", "ap_property"});
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
				new String[] {"top", "ap_property"});
	}

	public void testPropertyParenExpr() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
				"module top ();\n" +
						"	logic a, b, clk, reset, thevar, thing;\n" +
						"	property p_prop ();\n" +
						"		@(posedge clk)\n" +
						"			disable iff(thevar)\n" +
						"			if(b == 1'b1) \n" +
						"				b == b\n" +
						"			else\n" +
						"				b == 0;  // Flagging ; as an error, expected endproperty\n" +
						"	endproperty\n" +
						"	cover property ( @(posedge clk)\n" +
						"		disable iff (reset) \n" +
						"			(thing !== '0))\n" +
						"		begin  \n" +
						"			$display (\"a message\");\n" +
						"			$display (\"a message\");\n" +
						"		end\n" +
						"	cover property ( @(posedge clk)\n" +
						"			disable iff (reset) \n" +
						"			(thing !== '0)) some_inst.thing.sample(thing2);\n" +
						"endmodule\n"
						;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top", "p_prop"});
	}
	
	public void testPropertyBus() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module top ();\n" +
			"	logic a, b, clk, reset, thevar, thing;\n" +
			"	property some_prop_p;\n" +
			"	@ (posedge clk) disable iff (disable_assertions) (a==0) |->\n" +
			"	(\n" +
			"	|{b,c} == '0\n" +
			"	);\n" +
			"	endproperty\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top", "some_prop_p"});
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
			"	property a_prop ();\n" +
			"		@(posedge clk) \n" +
			"			$rose(thing) |-> \n" +
			"			(abus[(17):16]) == (abus);\n" +
			"	endproperty\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top", "some_prop", "a_prop"});
	}

	public void testPropertyArrayRange() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
				"module top ();\n" +
						"	logic clk, signala, signalb;\n" +
						"	property a_prop ();\n" +
						"		@(posedge clk) \n" +
						"			$rose(thing) |-> \n" +
						"			(abus[(16*1)+:16]) == (abus);\n" +
						"	endproperty\n" +
						"	property a_prop2 ();\n" +
						"		@(posedge clk) \n" +
						"			$rose(thing) |-> \n" +
						"			(abus[(16*1)-:16]) == (abus);\n" +
						"	endproperty\n" +
						"endmodule\n"
						;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"top", "a_prop", "a_prop2"});
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
				new String[] {"AssertionErrors", "p_example_1", "a_example_1"});
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
				new String[] {"t", "p_delay"});
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
			"  property some_prop;\n" +
			"		@(posedge clk)\n" +
			"			first_match	(##[1:2] $fell(sig1)) |=>@(posedge sig1) (sig2 == bus3[14]) ; \n" +
			"  endproperty\n" +
			"endmodule\n"
			;

		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test", "some_prop"});
	}	

	public void testPropertyAssign() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module test ();\n" +
					"	logic [15:0]A;\n" +
					"	logic [15:0]B;\n" +
					"	logic C,clk;\n" +
					"\n" +
					"	property p_prop;\n" +
					"		logic [15:0]A_temp ;\n" +
					"		logic [15:0]B_temp ;\n" +
					"		@ (negedge clk) \n" +
					"			(\n" +
					"				$rose(B) ##1 (1'b1),\n" +
					"				A_temp    = A,\n" +
					"				B_temp    = B\n" +
					"			)\n" +
					"			|=> @ (negedge C)\n" +
					"			(\n" +
					"				(A == A_temp) && \n" +
					"				(B == B_temp)\n" +
					"			);\n" +
					"	endproperty	\n" +
					"endmodule \n"
						;
		
		ParserTests.runTestStrDoc(testname, doc, 
				new String[] {"test", "p_prop"});
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
				new String[] {"top", "some_prop"});
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
				new String[] {"test", "some_prop"});
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
				new String[] {"test", "some_prop"});
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
				new String[] {"t", "ERROR_DEND_IS_UNKNOWN", "ERROR_DATA_IS_UNKNOWN"});
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
				new String[] {"t", "some_prop"});
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
				new String[] { "test", "s_error" });
	}
	
	
	public void testSequenceIfElse() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
					"module top ();\n" +
					"	sequence s_trig_seq (bit a, bit b, bit c, bit d);\n" +
					"		(a==1) ?\n" +
					"			(b==1) :\n" +
					"			(c==1);\n" +
					"	endsequence\n" +
					"endmodule\n"
					;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top", "s_trig_seq" });
	}
	public void testCycleDelayConstantExpression() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module top (); \n" +
				"	property p_prop (bit clk, bit a, bit b);\n" +
				"		@(posedge clk) disable iff (a)\n" +
				"				$rose(a) |-> ##(1) (a == b);\n" +
				"	endproperty\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top", "p_prop" });
	}

	public void testConstPostImplicationOp() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module top ();\n" +
				"	property p_prop (bit a, bit clk);\n" +
				"		@(posedge clk) disable iff (~a)\n" +
				"			$rose(a) |-> 1'b1 @(posedge clk);\n" +
				"	endproperty: p_prop\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top", "p_prop" });
	}
	
	public void testConstantAfterImplicationOp() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
					"module top ();\n" +
					"	property p_prop (bit a, bit clk);\n" +
					"		@(posedge clk) disable iff (~a)\n" +
					"				$rose(a) |-> 1'b1 @(posedge clk);\n" +
					"	endproperty: p_prop\n" +
					"endmodule\n"
					;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top", "p_prop" });
	}

	public void testIfAfterAt() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module top ();\n" +
				"	logic [1:0] abus;\n" +
				"	assert property (\n" +
				"			@(abus[1])\n" +
				"			1'b1 |->\n" +
				"			@(posedge abus[1])\n" +
				"			if(abus[1])\n" +
				"			##[0:5] (abus[1] === 1'b1)\n" +
				"			else\n" +
				"			##[0:2](abus[1] === 1'b1)\n" +
				"		);\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "top" });
	}

	public void testDisableIFF() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module m();\n" +
				"	logic reset, clk;\n" +
				"	property some_prop (logic [3:0] reg_bit) ;\n" +
				"		disable iff (reset)\n" +
				"			@(posedge clk)\n" +
				"			$rose (reg_bit) |=> @(posedge clk) ##2 reg_bit;\n" +
				"	endproperty: some_prop\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "m" });
	}
	
	public void testExpectStmt() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module m();\n" +
				"	logic clk, a_signal;\n" +
				"	task t ();\n" +
				"		begin\n" +
				"			expect( \n" +
				"					@(posedge clk) \n" +
				"					a_signal \n" +
				"				)   // Parser error on ## \n" +
				"			else begin  // Indent error ... else should not be indented\n" +
				"				$display(\"mismatch event\");\n" +
				"			end   // indent error, indent once more\n" +
				"		end\n" +
				"	endtask\n" +
				"endmodule\n"
						;
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] { "m" });
	}
}
