package net.sf.sveditor.core.tests.indent;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndentAssertions extends SVCoreTestCaseBase {
	
	public void testProperty() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"module bob ();\n" +
			"	logic thevar, clk, b;\n" +
			"	property p_property (somevar);\n" +
			"		@ (posedge clk)\n" +
			"			(b === 'h0);\n" +
			"	endproperty: p_property\n" +
			"\n" +
			"	ap_thing:\n" +
			"	assert property (p_property (thevar)) \n" +
			"	begin\n" +
			"		a.sample ();\n" +
			"	end\n" +
			"	else\n" +
			"	begin\n" +
			"		$display (\"thing is %b\");\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		IndentTests.runTest(getName(), fLog, doc);
	}

}
