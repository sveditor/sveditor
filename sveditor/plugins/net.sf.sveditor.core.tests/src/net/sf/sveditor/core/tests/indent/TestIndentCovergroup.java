package net.sf.sveditor.core.tests.indent;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndentCovergroup extends SVCoreTestCaseBase {
	
	public void testCovergroup() {
		String expected =
				"class foobar;\n" +
				"	\n" +
				"	covergroup foobar;\n" +
				"		\n" +
				"		var_cp : coverpoint (var) iff (var_cond);\n" +
				"		var1_cp : coverpoint (var) iff (var_cond);\n" +
				"		var2_cp : coverpoint (var) iff (var_cond) {\n" +
				"			bins subrange1[] = {[0:3]};\n" +
				"			bins subrange2[] = {\n" +
				"				[0:3],\n" +
				"				[4:7]\n" +
				"			};\n" +
				"		}\n" +
				"	endgroup\n" +
				"	covergroup cg_1;\n" +
				"		cp_3: coverpoint \n" +
				"			{\n" +
				"				top.bit1,\n" +
				"				top.bit2\n" +
				"			} {\n" +
				"				wildcard bins bin_0 = {2'b?0};\n" +
				"				wildcard bins bin_1 = {2'b?1};\n" +
				"			}\n" +
				"	endgroup\n" +
				"endclass\n";		

		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, expected);
	}

}
