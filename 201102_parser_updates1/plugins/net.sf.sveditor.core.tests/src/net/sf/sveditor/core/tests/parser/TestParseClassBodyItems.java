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

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
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
		runTest("testTaskFunction", content, 
				new String[] {"foobar", "foo_func", "foo_func_e", "foo_task"});
	}
	
	public void testSingleParameterClass() {
		String content =
			"class ovm_random_stimulus #(type T=ovm_transaction) extends ovm_component;\n" +
			"endclass\n"
			;
		
		runTest("testSingleParameterClass", content, 
				new String[] {"ovm_random_stimulus"});
	}

	public void testSimpleExtensionClass() {
		String content =
			"class ovm_random_stimulus extends ovm_component;\n" +
			"endclass\n"
			;
		
		runTest("testSingleParameterClass", content, 
				new String[] {"ovm_random_stimulus"});
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
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testTypedClassParameters", content, 
				new String[] {"foobar", "foo_func", "foo_func_e", "foo_task"});
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
		runTest("testFunctionVirtualIfcParam", content, 
				new String[] {"foo_func"});
		/*
		SVDBFile file = SVDBTestUtils.parse(content, "testFunctionVirtualIfcParam");
		
		SVDBClassDecl foobar_c = null;
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		for (ISVDBItemBase it_t : file.getItems()) {
			if (it_t.getType() == SVDBItemType.ClassDecl &&
					SVDBItem.getName(it_t).equals("foobar")) {
				foobar_c = (SVDBClassDecl)it_t;
			} else if (it_t.getType() == SVDBItemType.Marker &&
					SVDBItem.getName(it_t).equals(SVDBMarker.MARKER_ERR)) {
				errors.add((SVDBMarker)it_t);
				System.out.println("[ERROR] " + ((SVDBMarker)it_t).getMessage());
			}
		}

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo_func");

		assertEquals("Errors", 0, errors.size());
		
		assertNotNull(foobar_c);
		
		SVDBTask foo_func = null;
		for (ISVDBItemBase it_t : foobar_c.getItems()) {
			if (it_t.getType() == SVDBItemType.Function &&
					SVDBItem.getName(it_t).equals("foo_func")) {
				foo_func = (SVDBTask)it_t;
			}
		}
		
		assertNotNull(foo_func);
		 */
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
	
		runTest("testClassFields", content, new String[] {
				"__sv_builtin_covergroup_options",
				"weight", "goal", "name", "comment",
				"at_least", "detect_overlap", 
				"auto_bin_max", "per_instance",
				"cross_num_print_missing"});
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

		runTest("testBuiltinExternTasks", content, new String[] {"process"});
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
		
		SVDBClassDecl cg_options = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("__sv_builtin_covergroup_options")) {
				cg_options = (SVDBClassDecl)it;
			}
//			System.out.println("Item: " + it.getType() + " " + it.getName());
		}
		
		assertNotNull("Failed to find class __sv_builtin_covergroup_options", cg_options);
		
		for (ISVDBItemBase it : cg_options.getItems()) {
			System.out.println("    Item: " + it.getType() + " " + SVDBItem.getName(it));
			assertNotNull("Item " + SVDBItem.getName(it) + " does not have a location",
					it.getLocation());
			if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
				assertNotNull("Field " + SVDBItem.getName(it) + " does not have a type", 
						((SVDBVarDeclStmt)it).getTypeInfo());
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
		
		SVDBClassDecl foobar = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}

		SVDBTypedefStmt foobar_td = null;
		ISVDBItemBase foobar_i = null;
		
		for (ISVDBItemBase it : foobar.getItems()) {
			if (SVDBItem.getName(it).equals("foobar_t")) {
				foobar_i = it;
			}
		}
		
		assertNotNull("Failed to find foobar_t", foobar_i);
		assertEquals("foobar_t is of wrong type", 
				foobar_i.getType(), SVDBItemType.TypedefStmt);
		
		foobar_td = (SVDBTypedefStmt)foobar_i;

		assertEquals("foobar_t type-info is of wrong type",
				SVDBItemType.TypeInfoEnum, foobar_td.getTypeInfo().getType());
		
		SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)foobar_td.getTypeInfo();
		assertEquals("foobar_t doesn't have correct number of elements",
				2, enum_t.getEnumValues().first().size());
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
		
		SVDBClassDecl foobar = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}

		SVDBTypedefStmt foobar_td = null;
		ISVDBItemBase foobar_i = null;
		ISVDBItemBase foobar_i1 = null;
		
		for (ISVDBItemBase it : foobar.getItems()) {
			if (SVDBItem.getName(it).equals("other_foo_t")) {
				foobar_i = it;
			} else if (SVDBItem.getName(it).equals("other_foo_t1")) {
				foobar_i1 = it;
			}
		}
		
		assertNotNull("Failed to find other_foo_t", foobar_i);
		assertNotNull("Failed to find other_foo_t1", foobar_i1);
		assertEquals("other_foo_t is of wrong type", 
				foobar_i.getType(), SVDBItemType.TypedefStmt);
		
		foobar_td = (SVDBTypedefStmt)foobar_i;

		assertEquals("other_foo_t type-info is of wrong type",
				SVDBItemType.TypeInfoFwdDecl, foobar_td.getTypeInfo().getType());
	}

	public void testCovergroup() {
		String content = 
			"class foobar;\n" +
			"\n" +
			"\n" +
			"    int a, b, c;\n" +
			"\n" +
			"    covergroup cg;\n" +
			"        a_cp : coverpoint a;\n" +
			"        b_cp : coverpoint b {\n" +
			"            bins b[] = {[2:10]};\n" +
			"        }\n" +
			"        a_b_cross : cross a_cp, b_cp;\n" +
			"    endgroup\n" +
			"\n" +
			"    covergroup cg2;\n" +
			"        a_cp : coverpoint a;\n" +
			"        b_cp : coverpoint b {\n" +
			"            bins b[] = {[2:10]};\n" +
			"        }\n" +
			"        a_b_cross : cross a_cp, b_cp;\n" +
			"    endgroup\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBClassDecl foobar = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBCovergroup cg = null, cg2 = null;
		for (ISVDBItemBase it : foobar.getItems()) {
			if (SVDBItem.getName(it).equals("cg")) {
				cg = (SVDBCovergroup)it;
			} else if (SVDBItem.getName(it).equals("cg2")) {
				cg2 = (SVDBCovergroup)it;
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
		
		SVDBClassDecl foobar = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBConstraint empty_c = null;
		for (ISVDBItemBase it : foobar.getItems()) {
			if (SVDBItem.getName(it).equals("empty_c")) {
				empty_c = (SVDBConstraint)it;
			}
		}
		
		assertNotNull(empty_c);
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}

}
