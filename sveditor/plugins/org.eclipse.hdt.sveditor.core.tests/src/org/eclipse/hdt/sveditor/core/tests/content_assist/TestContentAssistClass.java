/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistClass extends SVCoreTestCaseBase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistExternTaskClass() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"class my_class2;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_<<MARK>>\n" +
			"endtask\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"m_field");
	}

	public void testIgnoreForwardDecl() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"typedef class foobar;\n" +
			"\n" +
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	task my_task();\n" +
			"		foobar v;\n" +
			"\n" +
			"		v.A<<MARK>>\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	public void testIgnoreNullStmt() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"typedef class foobar;\n" +
			"\n" +
			"class foobar;\n" +
			"	int		AAAA;;\n" +
			"	int		AABB;\n" +
			"	constraint c {\n" +
			"	};\n" + // The ';' in this case is a null statement
			"	;\n" +
			"	;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	task my_task();\n" +
			"		foobar v;\n" +
			"\n" +
			"		v.A<<MARK>>\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}
	
	public void testContentAssistExternTaskClassField() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_field.AA<<MARK>>\n" +
			"endtask\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	public void testContentAssistSuperSuperClass() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2;\n" +
			"\n" +
			"	function void build();\n" +
			"		super.<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n"
			;
	
		ContentAssistTests.runTest(this, doc, 
				"AAAA", "AABB",
				"BBBB", "BBCC",
				"CCCC", "CCDD");
	}

	public void testContentAssistSuperClass_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"module foo;\n" +
			"endmodule\n" +
			"\n" +
			"function void bar;\n" +
			"endfunction\n" +
			"\n" +
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends <<MARK>>\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"base", "super_1", "super_2");
	}
	
	public void testContentAssistBaseClass() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends s<<MARK>>\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"endclass\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"super_1", "super_2");
	}

	public void testContentAssistBaseClassEOF() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends s<<MARK>>"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"super_1", "super_2");
	}
	
	public void testContentAssistOnlyTopNew_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"	function new(int p1, int p2, int p3);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"	function new(int p1, int p2);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2 #(5);\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"\n" +
			"	function new(int p1);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		my_class f = n<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"new");
	}

	public void testContentAssistOnlyTopNew_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"	function new(int p1, int p2, int p3);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"	function new(int p1, int p2);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2 #(5);\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"\n" +
			"	function new(int p1);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"module top;\n" +
			"	function foo;\n" +
			"		my_class f = n<<MARK>>\n" +
			"	endfunction\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"new");
	}

	public void testStaticTypeAssist_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_ba<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"m_base");
	}
	
	public void testStaticTypeAssist_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base.AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}
	
	public void testStaticTypeAssist_3() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	static int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	public void testStaticTypeAssist_4() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA");
	}
	
	// Ensure that the expression-traversal code correctly
	// excludes non-static fields when referenced in a static way
	public void testStaticTypeAssist_5() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc 
				);
	}	

	// Ensure that content assist is able to traverse typedefs
	public void testStaticTypeAssist_6() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	static function int create();\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	typedef base		type_id;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::type_id::cr<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc,
				"create");
	}
	
	public void testParameterizedTypeAssist_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base #(int A=1, int B=2);\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		base#(1,4)::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc,
				"AAAA");
	}	
	
	public void testParameterizedTypeAssist_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base #(int A=1, int B=2);\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		base#(1,4) c;" +
			"		c.AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc,
				"AABB");
	}

	public void testContentAssistIgnoreBaseClassTF() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"class my_class2;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_<<MARK>>\n" +
			"endtask\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc,
				"m_field");
	}
	
	public void testContentAssistOnlyTopTF_1() {
		String testname = "testContentAssistOnlyTopTF_1";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	function AABB();\n" +
			"	endfunction\n" +
			"\n" +
			"	function BBAA();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	function AABB();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	function foo;\n" +
			"		super_1 f;\n" +
			"		f.AA<<MARK>>\n" +
			"	endfunction\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	public void testContentAssistOnlyTopTF_2() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	virtual task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	virtual function AABB();\n" +
			"	endfunction\n" +
			"\n" +
			"	virtual function BBAA();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	virtual task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	virtual function AABB();\n" +
			"		AAA<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AAAA");
	}
}


