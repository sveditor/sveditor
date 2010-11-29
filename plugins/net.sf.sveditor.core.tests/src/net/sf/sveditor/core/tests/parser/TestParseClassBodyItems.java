/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.tests.SVDBTestUtils;

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
		SVDBFile file = SVDBTestUtils.parse(content, "testTaskFunction");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, 
				"foobar", "foo_func", "foo_func_e", "foo_task");
	}

	public void testTypedClassParameters() {
		String content = 
			"`define PARAMS \\\n" +
			"    #(int A=5, \\\n" +
			"      bit[foo:0] B=pkg::func(a*7), \\\n" +
			"      int C=7)\n" +
			"\n" +
			"class foobar `PARAMS;\n" +
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
		SVDBFile file = SVDBTestUtils.parse(content, "testTypedClassParameters");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, 
				"foobar", "foo_func", "foo_func_e", "foo_task");
	}

	public void testFunctionVirtualIfcParam() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"    function void foo_func(virtual interface vi p);\n" +
			"        a = 5;\n" +
			"        b = 6;\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"endclass\n";
		SVDBFile file = SVDBTestUtils.parse(content, "testFunctionVirtualIfcParam");
		
		SVDBModIfcClassDecl foobar_c = null;
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		for (SVDBItem it_t : file.getItems()) {
			if (it_t.getType() == SVDBItemType.Class &&
					it_t.getName().equals("foobar")) {
				foobar_c = (SVDBModIfcClassDecl)it_t;
			} else if (it_t.getType() == SVDBItemType.Marker &&
					it_t.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
				errors.add((SVDBMarkerItem)it_t);
				System.out.println("[ERROR] " + ((SVDBMarkerItem)it_t).getMessage());
			}
		}

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo_func");

		assertEquals("Errors", 0, errors.size());
		
		assertNotNull(foobar_c);
		
		SVDBTaskFuncScope foo_func = null;
		for (SVDBItem it_t : foobar_c.getItems()) {
			if (it_t.getType() == SVDBItemType.Function &&
					it_t.getName().equals("foo_func")) {
				foo_func = (SVDBTaskFuncScope)it_t;
			}
		}
		
		assertNotNull(foo_func);
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
	
		SVDBFile file = SVDBTestUtils.parse(content, "testClassFields");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file,
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
			
		SVDBFile file = SVDBTestUtils.parse(content, "testBuiltinExternTasks");
		
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
		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
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

		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl foobar = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foobar")) {
				foobar = (SVDBModIfcClassDecl)it;
				break;
			}
		}

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

	public void testTypedefClass() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"    typedef class other_foo_t;\n" +
			"    typedef class other_foo_t1;\n" +
			"    typedef class other_foo_t2;\n" +
			"    typedef class other_foo_t3;\n" +
			"    typedef class other_foo_t4;\n" +
			"\n" +
			"    other_foo_t	    foo_f;" +
			"\n" +
			"endclass\n"
			;

		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl foobar = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foobar")) {
				foobar = (SVDBModIfcClassDecl)it;
				break;
			}
		}

		SVDBTypedef foobar_td = null;
		SVDBItem foobar_i = null;
		SVDBItem foobar_i1 = null;
		
		for (SVDBItem it : foobar.getItems()) {
			if (it.getName().equals("other_foo_t")) {
				foobar_i = it;
			} else if (it.getName().equals("other_foo_t1")) {
				foobar_i1 = it;
			}
		}
		
		assertNotNull("Failed to find other_foo_t", foobar_i);
		assertNotNull("Failed to find other_foo_t1", foobar_i1);
		assertEquals("other_foo_t is of wrong type", 
				foobar_i.getType(), SVDBItemType.Typedef);
		
		foobar_td = (SVDBTypedef)foobar_i;

		assertEquals("other_foo_t type-info is of wrong type",
				SVDBDataType.FwdDecl, foobar_td.getTypeInfo().getDataType());
	}

	public void testCovergroup() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"\n" +
			"    int a, b, c;\n" +
			"\n" +
			"    covergroup cg;\n" +
			"        a_cp : a;\n" +
			"        b_cp : b {\n" +
			"            bins b[] = {[2:10]};\n" +
			"        }\n" +
			"        a_b_cross : cross a_cp, b_cp;\n" +
			"    endgroup\n" +
			"\n" +
			"    covergroup cg2;\n" +
			"        a_cp : a;\n" +
			"        b_cp : b {\n" +
			"            bins b[] = {[2:10]};\n" +
			"        }\n" +
			"        a_b_cross : cross a_cp, b_cp;\n" +
			"    endgroup\n" +
			"\n" +
			"endclass\n"
			;

		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBModIfcClassDecl foobar = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foobar")) {
				foobar = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBCoverGroup cg = null, cg2 = null;
		for (SVDBItem it : foobar.getItems()) {
			if (it.getName().equals("cg")) {
				cg = (SVDBCoverGroup)it;
			} else if (it.getName().equals("cg2")) {
				cg2 = (SVDBCoverGroup)it;
			}
		}
		
		assertNotNull(cg);
		assertNotNull(cg2);
	}

	public void testEmptyConstraint() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"\n" +
			"    int a, b, c;\n" +
			"\n" +
			"    constraint empty_c {}\n" +
			"\n" +
			"endclass\n"
			;

		SVDBFile file = SVDBTestUtils.parse(content, "testEmptyConstraint");
		
		SVDBModIfcClassDecl foobar = null;
		for (SVDBItem it : file.getItems()) {
			if (it.getName().equals("foobar")) {
				foobar = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBConstraint empty_c = null;
		for (SVDBItem it : foobar.getItems()) {
			if (it.getName().equals("empty_c")) {
				empty_c = (SVDBConstraint)it;
			}
		}
		
		assertNotNull(empty_c);
	}

}
