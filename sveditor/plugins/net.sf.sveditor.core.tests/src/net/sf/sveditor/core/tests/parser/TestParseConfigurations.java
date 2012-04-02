package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import junit.framework.TestCase;

public class TestParseConfigurations extends TestCase {
	
	public void testConfig_33_2_1() {
		SVCorePlugin.getDefault().enableDebug(true);
		String testname = "testConfig_33_2_1";
		String content =
			"config cfg1; // specify rtl adder for top.a1, gate-level adder for top.a2\n" +
			"	design rtlLib.top;\n" +
			"	default liblist rtlLib;\n" +
			"	instance top.a2 liblist gateLib;\n" +
			"endconfig\n" 
			;
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"cfg1"});
	}
	
	public void testConfig_33_2_2() {
		SVCorePlugin.getDefault().enableDebug(true);
		String testname = "testConfig_33_2_2";
		String content =
			"config cfg2;\n" +
			"	localparam S = 24;\n" +
			"	design rtlLib.top4;\n" +
			"	instance top4.a1 use #(.W(top4.S));\n" +
			"	instance top4.a2 use #(.W(S));\n" +
			"endconfig\n"
			;
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"cfg2"});
	}

}
