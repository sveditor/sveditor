package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestParseBind extends TestCase {
	
	public void testBasicBind() throws SVParseException {
		String testname = "testBasicBind";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind target_scope monitor m1(.a, .b, .c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"m1"});
	}

	public void testLRMEx1() throws SVParseException {
		String testname = "testLRMEx1";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"module t;\n" +
			"	bind cpu: cpu1 fpu_props fpu_rules_1(a, b, c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"fpu_rules_1"});
	}

	public void testLRMEx2() throws SVParseException {
		String testname = "testLRMEx2";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind cpu: cpu1, cpu2, cpu3 fpu_props fpu_rules_1(a, b, c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"fpu_rules_1"});
	}

}
