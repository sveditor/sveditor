package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestParseRandsequence extends SVCoreTestCaseBase {
	
	public void testRandsequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc =
			"class rs1;\n" +
			"\n" +
			"	task rs_t();\n" +
			"		randsequence( main )\n" +
			"			main : first second done ;\n" +
			"			first : add | dec ;\n" +
			"			second : pop | push ;\n" +
			"			done : { $display(\"done\"); } ;\n" +
			"			add : { $display(\"add\"); } ;\n" +
			"			dec : { $display(\"dec\"); } ;\n" +
			"			pop : { $display(\"pop\"); } ;\n" +
			"			push : { $display(\"push\"); } ;\n" +
			"		endsequence\n" +
			"	endtask\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"rs1", "rs_t"});
	}

}
