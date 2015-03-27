package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestParseSpecify extends TestCase {
	
	public void testSpecifyIf() throws SVParseException {
		String testname = "testSpecifyIf";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module my_module(input logic some_input, output logic DOUT);\n" +
				" logic DOUT_i, normal_read_access;\n" +
				" specify\n" +
				" 	specparam Tdh = 10,\n" +
				" 	Tacc = 10;\n" +
				" 		// specify some delay\n" +
				" 		if (normal_read_access) (posedge some_input => (DOUT:DOUT_i)) = (Tacc, Tacc,Tdh); // unpexpected if statement\n" +
				" 	endspecify " +
				" endmodule\n"
				;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"my_module"});
	}

	public void testSpecifyBlock() throws SVParseException {
		String testname = "testSpecifyBlock";
		String doc = 
				"module delay (in, in1, in2, out, out1, out2, out3, RD, CLK);\n" +
				"	input  in, in1;\n" +
				"	input [1:0] in2;\n" +
				"	output out, out1, out2;\n" +
				"	output [1:0] out3;\n" +
				"	input RD, CLK;\n" +
				"				\n" +
				"	assign out = in;\n" +
				"				\n" +
				"	specify\n" +
				"		(in => out) = (600,600);\n" +
				"		(in +=> out) = (600,600);\n" +
				"		(in -=> out) = (600,600);\n" +
				"		(in1,in2[1]  *> out      ) = (600,600); // multi-to-single\n" +
				"		(in1,in2  *> (out-:out2)) = (600,600); // multi-to-range\n" +
				"		(in1,in2  *> (out+:out2)) = (600,600); // multi-to-range\n" +
				"		(in1,in2  *> (out :out2)) = (600,600); // multi-to-range\n" +
				"		(in      -*> out1,out2) = (600,600); // single-to-multi\n" +
				"		(in1,in2 +*> out1,out2) = (600,600); //multi-to-multi\n" +
				"		if (RD==1) (posedge CLK *> (out3[1]:out3[0])) = (600,600); //multi-to-multi\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTestStrDoc(testname, doc, new String[] {"delay"});
	}
	
	public void testSpecifyBlock_2() throws SVParseException {
		String testname = "testSpecifyBlock_2";
		String doc =
				"module delay;\n" +
				"        specify\n" +
				" specparam normal_scl_low  = 4700,\n" +
				" normal_scl_high = 4000,\n" +
				" normal_tsu_sta  = 4700,\n" + // 5
				" normal_thd_sta  = 4000,\n" +
				" normal_tsu_sto  = 4000,\n" +
				" normal_tbuf     = 4700,\n" +
				" fast_scl_low  = 1300,\n" +
				" fast_scl_high =  600,\n" + // 10
				" fast_tsu_sta  = 1300,\n" +
				" fast_thd_sta  =  600,\n" +
				" fast_tsu_sto  =  600,\n" +
				" fast_tbuf     = 1300;\n" +
				"\n" + // 15
				" $width(negedge scl, normal_scl_low);  // scl low time\n" +
				" $width(posedge scl, normal_scl_high); // scl high time\n" +
				" $setup(posedge scl, negedge sda &&& scl, normal_tsu_sta); // setup start\n" +
				" $setup(negedge sda &&& scl, negedge scl, normal_thd_sta); // hold start\n" +
				" $setup(posedge scl, posedge sda &&& scl, normal_tsu_sto); // setup stop\n" + // 20
				" $setup(posedge tst_sta, posedge tst_sto, normal_tbuf); // stop to start time\n" +
				" endspecify\n" +
				"endmodule\n" 
				;
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTestStrDoc(testname, doc, new String[] {"delay"});
	}

	public void testSpecifyBlock_CondMinTyp() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module delay;\n" +
				"	specify\n" +
				"		if ((a == 1'b0) && (b == 1'b1))\n" +
				"			(clk => q)=(1.000, 1.000);\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"delay"});
	}
	
	public void testSpecifyBlock_CondMinTyp_1() throws SVParseException {
		String testname = "testSpecifyBlock";
		String doc = 
				"module delay;\n" +
				"	specify\n" +
				"		if (a == 1'b0)\n" +
				"			(clk => q)=(1.000, 1.000);\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTestStrDoc(testname, doc, new String[] {"delay"});
	}

	public void testSpecifyArrayIfCond() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module delay;\n" +
				"	specify\n" +
				"		if (thing[0] == 1'b0)\n" +
				"			(CLK => Q[15])=(1.000, 1.000);\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"delay"});
	}
	
	public void testSpecifyPlusGE() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module delay;\n" +
				"	specify\n" + 
				"		(in +=> out ) = (0.0,0.0);\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"delay"});
	}

	public void testSpecifyMinusGE() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module delay;\n" +
				"	specify\n" + 
				"		(in -=> out ) = (0.0,0.0);\n" +
				"	endspecify\n" +
				"endmodule\n"
				;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"delay"});
	}
}
