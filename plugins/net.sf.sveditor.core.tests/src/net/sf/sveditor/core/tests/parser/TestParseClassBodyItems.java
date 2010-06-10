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
			"        c = 5;\n" +
			"        d = 6;\n" +
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
	
	public void testClassFields() {
		String content = 
		"class __sv_builtin_covergroup_options;\n" +
		"	int 	weight;\n" + 
		"\n" +
		"	real 	goal;\n" +
		"\n" +
		"	string 	name;\n" +
		"\n" +
		"	string 	comment;\n" +
		"\n" +
		"	int		at_least;\n" +
		"\n" +
		"	bit		detect_overlap;\n" +
		"\n" +
		"	int		auto_bin_max;\n" +
		"\n" +
		"	bit		per_instance;\n" +
		"\n" +
		"	bit		cross_num_print_missing;\n" +
		"\n" +
		"endclass\n";
	
		SVDBFile file = ParserTests.parse(content, "testClassFields");
		
		ParserTests.assertNoErrWarn(file);
		ParserTests.assertFileHasElements(file,
				"__sv_builtin_covergroup_options",
				"weight", "goal", "name", "comment",
				"at_least", "detect_overlap", 
				"auto_bin_max", "per_instance",
				"cross_num_print_missing");
	}

}
