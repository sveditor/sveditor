package net.sf.sveditor.core.tests.hierarchy;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;

public class TestModuleHierarchy extends TestCase {

	public void testModuleSubHierarchy() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m1;\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" +
			"	m1 m1_1();\n" +
			"	m1 m1_2();\n" +
			"endmodule\n" +
			"\n" +
			"module m3;\n" +
			"	m2 m2_1();\n" +
			"	m2 m2_2();\n" +
			"endmodule\n" +
			"\n" +
			"module top;\n" +
			"	m3 m3_1();\n" +
			"	m3 m3_2();\n" +
			"	m3 m3_3();\n" +
			"endmodule\n" +
			"\n"
			;
		String testname = "testModuleSubHierarchy";
		
		HierarchyTests.runModuleHierarchyTest(testname, doc, "top", 
				"top.m3_1.m2_2.m1_1");
	}
}
