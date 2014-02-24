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
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseClassBodyItems extends TestCase {
	
	public void testTaskFunction() {
		SVCorePlugin.getDefault().enableDebug(false);
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

	public void testVirtualInterfaceFunction() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"interface my_if;\n" +
			"endinterface\n" +
			"\n" +
			"class foobar;\n" +
			"	virtual my_if	m_if;\n" +
			"\n" +
			"    function virtual my_if foo_func();\n" +
			"		return m_if;\n" +
			"    endfunction\n" + 
			"endclass\n";
		runTest("testTaskFunction", content, 
				new String[] {"my_if", "foobar", "foo_func"});
	}
	
	public void testTaskFunctionWithSoftArg() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"class foobar;\n" +
			"\n" +
			"    function void foo_func(int soft);\n" +
			"        a = 7;\n" +
			"        b = 6;\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"endclass\n";
		runTest("testTaskFunctionWithSoftArg", content, 
				new String[] {"foobar", "foo_func"});
	}

	public void testImplicitVectoredReturnFunction() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"function [7:0] get_cmdname (\n" +
			"		input integer command\n" +
			");\n" +
			"begin\n" +
			"end\n" +
			"endfunction\n" +
			"endclass\n"
			;
		runTest("testBeginEndFunction", content, 
				new String[] {"c", "get_cmdname"});
	}

	public void testEmptyClass() {
		String content = 
			"class class1;\n" +
			"\n" +
			"endclass";
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("testTaskFunction", content, new String[] {"class1"});
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

	public void testCovergroupSizedArrayBins() {
		String content =
			"class foo;\n" +
			"	covergroup cg;\n" +
			"		foo_cp : coverpoint foo_field {\n" +
			"			bins foo_field[8] = {[0:255]};\n" +
			"		}\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		
		runTest("testCovergroupSizedArrayBins", content, 
				new String[] {"foo", "cg"});
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
	
	public void testMultiParamClass() {
		String content = 
				"class my_class\n" +
				"#(\n" +
				"type vif = virtual my_inteface, // causes arse error\n" +
				"type data = pkg_mypackage::my_datatype\n" +
				") extends uvm_object;\n" +
				"\n" +
				"// class internals\n" +
				"\n" +
				"endclass\n" +
				"\n";
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testTypedClassParameters", content, 
				new String[] {"my_class"});
	}
	
	public void testNameMappedParamClassCall() {
		String content = 
				"class my_class;\n" +
				"	function void doit();\n" +
				"		foo = myclass #(.A(5), .B(int))::type_id::create();\n" +
				"	endfunction\n" +
				"\n" +
				"endclass\n" +
				"\n";
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest(getName(), content, 
				new String[] {"my_class", "doit"});
	}
	
	public void testAttrInstance() {
		String content = 
			"(*attr1=\"foo\", attr2=bar*)\n" +
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
	
	public void testIncompleteAttrInstance() {
		String content = 
			"(*attr1=\"foo\", \n" +
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
		runTestExpErr("testTaskFunction", content, 
				new String[] {"foobar", "foo_func", "foo_func_e", "foo_task"});
	}

	public void testAttrTaggedRandomize() {
		String content = 
			"class foobar;\n" +
			"	item_t item;\n" +
			"\n" +
			"    function void foo_func();\n" +
			"		item.randomize (* solvefaildebug *) ();\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"endclass\n";
		runTest("testAttrTaggedRandomize", content, 
				new String[] {"foobar", "item", "foo_func"});
	}

	public void testAttrTaggedRandomize2() {
		String content = 
			"class foobar;\n" +
			"	item_t item;\n" +
			"\n" +
			"    function void foo_func();\n" +
			"		item.randomize (* solvefaildebug *);\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"endclass\n";
		runTest("testAttrTaggedRandomize2", content, 
				new String[] {"foobar", "item", "foo_func"});
	}

	public void testAttrTaggedTF() {
		String content = 
			"class foobar;\n" +
			"	item_t item;\n" +
			"\n" +
			"    function void foo_func();\n" +
			"		foo_func (* solvefaildebug *) ();\n" +
			"    endfunction\n" + // endfunction without : <name>
			"\n" +
			"endclass\n";
		runTest("testTaskFunction", content, 
				new String[] {"foobar", "item", "foo_func"});
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
					SVDBItem.getName(it_t).equals(MarkerType.Error)) {
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
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"__sv_builtin class process;\n" +
			"\n" +
			"enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;\n" +
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
		LogHandle log = LogFactory.getLogHandle("testClassStringFields");
		SVDBFile file = SVDBTestUtils.parse(content, "testClassStringFields");
		
		SVDBClassDecl cg_options = null;
		for (ISVDBItemBase it : file.getChildren()) {
			if (SVDBItem.getName(it).equals("__sv_builtin_covergroup_options")) {
				cg_options = (SVDBClassDecl)it;
			}
			log.debug("Item: " + it.getType() + " " + SVDBItem.getName(it));
		}
		
		assertNotNull("Failed to find class __sv_builtin_covergroup_options", cg_options);
		
		for (ISVDBItemBase it : cg_options.getChildren()) {
			log.debug("    Item: " + it.getType() + " " + SVDBItem.getName(it));
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
		for (ISVDBItemBase it : file.getChildren()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}

		SVDBTypedefStmt foobar_td = null;
		ISVDBItemBase foobar_i = null;
		
		for (ISVDBItemBase it : foobar.getChildren()) {
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
				2, enum_t.getEnumerators().size());
	}
	
	public void testBeginBlockVirtualInterfaceVar() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testBeginBlockVirtualInterfaceVar";
		String content =
			"class tb_env;\n" +
			"	function void build;\n" +
			"		//------------------------------------------------\n" +
			"		// virtual interface\n" +
			"		//------------------------------------------------\n" +
			"		begin\n" +
			"			virtual pin_xactor_if #(1) int0_if;\n" +
			"		end\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"tb_env", "build"});
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
		for (ISVDBItemBase it : file.getChildren()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}

		SVDBTypedefStmt foobar_td = null;
		ISVDBItemBase foobar_i = null;
		ISVDBItemBase foobar_i1 = null;
		
		for (ISVDBItemBase it : foobar.getChildren()) {
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
		for (ISVDBItemBase it : file.getChildren()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBCovergroup cg = null, cg2 = null;
		for (ISVDBItemBase it : foobar.getChildren()) {
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
		for (ISVDBItemBase it : file.getChildren()) {
			if (SVDBItem.getName(it).equals("foobar")) {
				foobar = (SVDBClassDecl)it;
				break;
			}
		}
		
		assertNotNull(foobar);

		SVDBConstraint empty_c = null;
		for (ISVDBItemBase it : foobar.getChildren()) {
			if (SVDBItem.getName(it).equals("empty_c")) {
				empty_c = (SVDBConstraint)it;
			}
		}
		
		assertNotNull(empty_c);
	}

	public void testExternConstraint() {
		String testname = "testExternConstraint";
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	constraint i_cons; ///< Error reported here even though this is a legal system verilog constraint body declaration\n" +
				"endclass\n" +
				"\n" +
				"constraint my_class::i_cons {\n" +
				"	i>0;\n" +
				"}\n"
				;
		
		runTest(testname, content, new String[] {"my_class"});
	}

	public void testImplicationConstraint() {
		String testname = "testImplicationConstraint";
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	rand int j;\n" +
				"	constraint i_cons {\n" +
				"		i == 1 -> j == 2 ;\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		runTest(testname, content, new String[] {"my_class"});
	}

	public void testComplexImplicationConstraint() {
		String testname = "testComplexImplicationConstraint";
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	rand int j;\n" +
				"	constraint i_cons {\n" +
				"		i inside { 1, 2 } -> j == 2 ;\n" +
				"		i inside { 1, 2 } -> ( j inside { 3, 4 } ) ;\n" +
				"		i inside { 1, 2 } -> ( j inside { 3, 4 } && j inside { 5, 6 } ) ;\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		runTest(testname, content, new String[] {"my_class"});
	}

	public void testComplexImplicationConstraint2() {
		String testname = "testComplexImplicationConstraint2";
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	rand int j;\n" +
				"	rand int k;\n" +
				"	constraint i_cons {\n" +
				"		( i == j ) -> ( k dist { 0:=50, 1:=20, 2:=30 } ) ; " +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		SVParserConfig config = new SVParserConfig();
		config.setAllowDistInsideParens(true);
		
		runTest(config, testname, content, new String[] {"my_class"});
	}

	public void testComplexImplicationConstraint3() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	rand int j;\n" +
				"	rand int k[];\n" +
				"	constraint i_cons {\n" +
				"		( i == j ) -> foreach(k[idx]) k[idx] == 5;\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		SVParserConfig config = new SVParserConfig();
		config.setAllowDistInsideParens(true);
		
		runTest(config, testname, content, new String[] {"my_class"});
	}

	public void testMultiDimForeachConstraint() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int arr[4][4];\n" +
				"	constraint arr_c {\n" +
				"		foreach (arr[i, j]) {\n" +
				"			arr[i][j] == i+j;\n" +
				"       }\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		SVParserConfig config = new SVParserConfig();
		config.setAllowDistInsideParens(true);
		
		runTest(config, testname, content, new String[] {"my_class"});
	}

	public void testMultiDimForeachConstraint2() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int arr[4][4];\n" +
				"	constraint arr_c {\n" +
				"		foreach (this.arr[i,j]) {\n" +
				"			arr[i][j] == i+j;\n" +
				"       }\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		SVParserConfig config = new SVParserConfig();
		config.setAllowDistInsideParens(true);
		
		runTest(config, testname, content, new String[] {"my_class"});
	}

	public void testHierarchcalPathForeachConstraint2() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int arr[4][4];\n" +
				"	constraint arr_c {\n" +
				"		foreach (top.mid.mid_mid_arr[5].bottom_arr[4].arr[i,j]) {\n" +
				"			arr[i][j] == i+j;\n" +
				"       }\n" +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		SVParserConfig config = new SVParserConfig();
		config.setAllowDistInsideParens(true);
		
		runTest(config, testname, content, new String[] {"my_class"});
	}
	
	public void testIfConcatConstraint() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class pkt;\n" +
			"	rand bit one_beat;\n" +
			"	rand int len;\n" +
			"	rand bit [31:0] addr;\n" +
			"\n" +
			"	constraint wr_c {\n" +
			"		if (!one_beat) { addr[5:0] == 0, len == 15 };\n" +
			"	}\n" +
			"	endclass\n"
			;
		runTest(getName(), content, new String[] {"pkt"});
	}

	public void testIfConcatConstraint2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class pkt;\n" +
			"	rand bit one_beat;\n" +
			"	rand int len;\n" +
			"	rand bit [31:0] addr;\n" +
			"\n" +
			"	constraint wr_c {\n" +
			"		if (!one_beat) { addr[5:0] == 0 };\n" +
			"	}\n" +
			"	endclass\n"
			;
		runTest(getName(), content, new String[] {"pkt"});
	}
	
	public void testDistConstraint() {
		String testname = "testDistConstraint";
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	rand int j;\n" +
				"	rand int k;\n" +
				"	constraint i_cons {\n" +
				"		 k dist { 0:=50, 1:=20, 2:=30 } ; " +
				"	}\n" +
				"endclass\n" +
				"\n"
				;
		
		runTest(testname, content, new String[] {"my_class"});
	}
	
	public void testDistConstraint_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"	constraint c_corrupted_preamble {\n" +
			"		if (use_preamble_err == TRUE) {\n" +
            "			mac_frm.preamble.preamble_data[0] dist {8'h55 := 10, 8'hAA := 1, 8'h56 := 1, 8'h54 := 1, 8'hD5 := 1};\n" +
            "			foreach (mac_frm.preamble.preamble_data[i]) {\n" +
            "		    	if (i == mac_frm.preamble.len - 1) {\n" +
            "        			(mac_frm.preamble.preamble_data[0] == 8'h55) -> \n" +
            "           			mac_frm.preamble.preamble_data[i] dist {8'h55 := 1, 8'h56 := 1, 8'hAA := 1, 8'hFD := 1, 8'h54 := 1, 8'hD5 := 10};\n" +
            "       			(mac_frm.preamble.preamble_data[0] != 8'h55) -> \n" +
            "           			mac_frm.preamble.preamble_data[i] == 8'hD5;\n" +
            "   			} else if (i != 0) { }\n" +
            "			}\n" +
            "		}\n" +
            "	}\n" +
            "endclass\n" 
            ;
		runTest(getName(), content, new String[] {"my_class"});
	}
	
	public void testPotentialConcatConstraint() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"class my_class;\n" +
			"	constraint c_byte_len {  pif_xfer_data.size() == byte_len;\n" +
            "                 byte_len > 0; byte_len <= 12'hfff; \n" +
            "                 if( (pif_xfer_type == PIF_XFR_SINGLE_RD) || (pif_xfer_type == PIF_XFR_SINGLE_WR) )\n" +
            "                 {\n" +
            "                     if(EXT_DATA_WIDTH == 32) \n" +
            "                     {\n" +
            "                         byte_len inside {1,2,4}; \n" +
            "                     }\n" +
            "                     else if(EXT_DATA_WIDTH == 64) \n" +
            "                     {\n" +
            "                         byte_len inside {1,2,4,8};\n" +
            "                     }\n" +
            "                     else if(EXT_DATA_WIDTH == 128) \n" +
            "                     {\n" +
            "                         byte_len inside {1,2,4,8,16};\n" +
            "                     }\n" +
            "                 }           \n" +
            "                 else\n" +
            "                 {\n" +
            "                     byte_len == pif_xfer_length * (EXT_DATA_WIDTH/8);\n" +
            "                 }\n" +
            "             }\n" +
            "endclass\n"
            ;
		
		
		runTest(getName(), content, new String[] {"my_class"});
	}
	
	public void testSoftConstraint() {
		String testname = "testExternConstraint";
		String content = 
				"class my_class;\n" +
				"	rand int i;\n" +
				"	constraint i_cons {\n" +
				"     soft i == 2;"  +
				"   }\n" +
				"endclass\n" +
				"\n" 
				;
		
		runTest(testname, content, new String[] {"my_class"});
	}

	public void testRandomizeWithNoArgList() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testRandomizeWithNoArgList";
		String content = 
				"class my_class;\n" +
				"	function void my_func;\n" +
				"		my_class cls1;\n" + 
				"		assert(cls1.randomize with {\n" +
				"			cls1.a == 2;\n" +
				"		});" +
				"	endfunction\n" +
				"endclass\n"
				;
		
		runTest(testname, content, new String[] {"my_class", "my_func"});
	}

	public void testRandomizeWithArgList() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testRandomizeWithArgList";
		String content = 
				"class my_class;\n" +
				"	function void my_func;\n" +
				"		my_class cls1;\n" + 
				"		assert(cls1.randomize() with {\n" +
				"			cls1.a == 2;\n" +
				"		});" +
				"	endfunction\n" +
				"endclass\n"
				;
		
		runTest(testname, content, new String[] {"my_class", "my_func"});
	}

	public void testFindWithNoArgList() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testFindWithNoArgList";
		String content = 
				"class my_class;\n" +
				"	function void my_func;\n" +
				"		my_class cls1;\n" + 
				"		cls1.q.find with (item == idx);\n" +
				"	endfunction\n" +
				"endclass\n"
				;
		
		runTest(testname, content, new String[] {"my_class", "my_func"});
	}

	public void testFindWithArgList() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testFindWithArgList";
		String content = 
				"class my_class;\n" +
				"	function void my_func;\n" +
				"		my_class cls1;\n" + 
				"		cls1.q.find() with (item == idx);\n" +
				"	endfunction\n" +
				"endclass\n"
				;
		
		runTest(testname, content, new String[] {"my_class", "my_func"});
	}

	public void testRandomizeLocalVarRef() {
		String testname = "testRandomizeLocalVarRef";
		String content =
			"class myclass;\n" +
			"	typedef enum bit {\n" +
			"		ON,\n" +
			"		OFF\n" +
			"	}  on_off_e;\n" +
			"\n" +
			"	rand bit is_on_off_local;\n" +
			"	rand on_off_e is_on_off_enum;\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"module mymodule;\n" +
			"	logic a;\n" +
			"\n" +
			"	task sometask(input bit on);\n" +
			"		myclass mc;\n" +
			"			mc = new();\n" +
			"			void'(mc.randomize () with {\n" +
			"				is_on_off_local == local::on;\n" + // 19
			"				is_on_off_enum  == myclass::ON;\n" +
      		"			});\n" +
       		"	endtask\n" +
       		"endmodule\n"
       		;
		runTest(testname, content, new String[] {"myclass","mymodule"});
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		runTest(null, testname, doc, exp_items);
	}

	private void runTest(
			SVParserConfig	config,
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> result = SVDBTestUtils.parse(
				log, SVLanguageLevel.SystemVerilog, config, 
				new StringInputStream(doc), testname, markers);
		
		SVDBFile file = result.second();
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
	
	private void runTestExpErr(
			String			testname,
			String			doc,
			String			exp_items[]) {
		SVDBFile file = SVDBTestUtils.parse(doc, testname, true);
		
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}

}
