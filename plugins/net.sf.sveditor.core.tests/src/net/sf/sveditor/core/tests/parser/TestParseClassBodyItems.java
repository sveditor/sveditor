package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;

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
	
	public void testBuiltinExternTasks() {
		String content = 
			"__sv_builtin class process;\n" +
			"\n" +
			"enum state { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED };\n" +
			"\n" +
			"static extern function process self();\n" +
			"\n" +
			"extern function state status();\n" +
			"\n" +
			"extern function void kill();\n" +
			"\n" +
			"extern task await();\n" +
			"\n" +
			"extern function void suspend();\n" +
			"\n" +
			"extern task resume();\n" +
			"\n" +
			"endclass\n"
			;
			
		SVDBFile file = ParserTests.parse(content, "testBuiltinExternTasks");
		
		SVDBModIfcClassDecl process = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("process")) {
				process = (SVDBModIfcClassDecl)it;
			}
			System.out.println("Item: " + it.getType() + " " + it.getName());
		}
		
		assertNotNull("Failed to find class process", process);
		
		for (SVDBItem it : process.getItems()) {
			System.out.println("    Item: " + it.getType() + " " + it.getName());
		}
	}
	
	public void testClassStringFields() {
		String content = 
			"class __sv_builtin_covergroup_options;\n" +
			"int 	weight;\n" +
			"\n" +
			"real 	goal;\n" +
			"\n" +
			"string 	name;\n" +
			"\n" +
			"string 	comment;\n" +
			"\n" +
			"int		at_least;\n" +
			"\n" +
			"bit		detect_overlap;\n" +
			"\n" +
			"int		auto_bin_max;\n" +
			"\n" +
			"bit		per_instance;\n" +
			"\n" +
			"bit		cross_num_print_missing;\n" +
			"\n" +
			"endclass\n"
			;
		SVDBFile file = ParserTests.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl cg_options = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("__sv_builtin_covergroup_options")) {
				cg_options = (SVDBModIfcClassDecl)it;
			}
			System.out.println("Item: " + it.getType() + " " + it.getName());
		}
		
		assertNotNull("Failed to find class __sv_builtin_covergroup_options", cg_options);
		
		for (SVDBItem it : cg_options.getItems()) {
			System.out.println("    Item: " + it.getType() + " " + it.getName());
			assertNotNull("Item " + it.getName() + " does not have a location",
					it.getLocation());
			if (it.getType() == SVDBItemType.VarDecl) {
				assertNotNull("Field " + it.getName() + " does not have a type", 
						((SVDBVarDeclItem)it).getTypeInfo());
			}
		}
	}
	
	public void testTypedef() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"    typedef enum {\n" +
			"        FOO,\n" +
			"        BAR\n" +
			"    } foobar_t;\n" +
			"\n" +
			"\n" +
			"    foobar_t     foo_f;" +
			"\n" +
			"endclass\n"
			;

		SVDBFile file = ParserTests.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl foobar = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foobar")) {
				foobar = (SVDBModIfcClassDecl)it;
				break;
			}
		}

		SVDBTypeInfoEnum foobar_t = null;
		SVDBTypedef foobar_td = null;
		SVDBItem foobar_i = null;
		
		for (SVDBItem it : foobar.getItems()) {
			if (it.getName().equals("foobar_t")) {
				foobar_i = it;
			}
		}
		
		assertNotNull("Failed to find foobar_t", foobar_i);
		assertEquals("foobar_t is of wrong type", 
				foobar_i.getType(), SVDBItemType.Typedef);
		
		foobar_td = (SVDBTypedef)foobar_i;

		assertEquals("foobar_t type-info is of wrong type",
				SVDBDataType.Enum, foobar_td.getTypeInfo().getDataType());
		
		SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)foobar_td.getTypeInfo();
		assertEquals("foobar_t doesn't have correct number of elements",
				2, enum_t.getEnumValues().size());
	}
}
