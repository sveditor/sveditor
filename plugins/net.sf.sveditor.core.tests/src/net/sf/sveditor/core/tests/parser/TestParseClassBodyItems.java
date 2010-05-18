package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.db.SVDBFile;
import junit.framework.TestCase;

public class TestParseClassBodyItems extends TestCase {
	
	public void testTaskFunction() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"    function void foo_func();\n" +
			"        a = 5;\n" +
			"        b = 6;\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"    function void foo_func_e();\n" +
			"        a = 5;\n" +
			"        b = 6;\n" +
			"    endfunction:foo_func_e\n" + // endfunction without : <name>
			"\n" +
			"    task foo_task();\n" +
			"    endtask\n" +
			"endclass\n";
		SVDBFile file = ParserTests.parse(content, "testTaskFunction");
		
		ParserTests.assertNoErrWarn(file);
		ParserTests.assertFileHasElements(file, 
				"foobar", "foo_func", "foo_func_e", "foo_task");
	}

}
