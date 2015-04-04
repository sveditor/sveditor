package net.sf.sveditor.core.tests.indent;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndentConstraints extends SVCoreTestCaseBase {

	public void testIndentDistConstraint() {
		String doc = 
				"class someclass;\n" +
						"	constraint clock {\n" +
						"		clk_cfg.period dist {\n" +
						"			[1:10  ] :/ 1,\n" +
						"			11       := 1,\n" +
						"			12       := 1,\n" +
						"			[13: 15] :/ 1\n" +
						"		};\n" +
						"		clk_cfg.jitter < (3 * 1000);\n" +
						"	}\n" +
						"	function void my_func;\n" +
						"		my_class cls1; \n" +
						"		assert(cls1.randomize() with {\n" +
						"				cls1.a == 2;\n" +
						"			})\n" +
						"		else $display (\"ERROR\");\n" +
						"	endfunction\n" +
						"endclass\n"
						;				
		
		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, doc);
	}
}
