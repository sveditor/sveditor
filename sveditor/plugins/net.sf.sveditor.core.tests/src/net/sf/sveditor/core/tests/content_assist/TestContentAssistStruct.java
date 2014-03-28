/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistStruct extends SVCoreTestCaseBase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructTypedef() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} my_struct_t;\n" +
			"\n" +
			"class my_class;\n" +
			"    my_struct_t              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field");
	}

	/**
	 * Test that content assist on struct module ports works
	 */
	public void testContentAssistStructModuleInput() {
		SVCorePlugin.getDefault().enableDebug(false);

		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} my_struct_t;\n" +
			"\n" +
			"module foo_m(input my_struct_t mm);\n" +
			"\n" +
			"    function void foo();\n" +
			"        mm.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endmodule\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field");
	}

	/**
	 * Test that content assist on struct module ports works
	 * In this case, ensure that a parse error from the missing
	 * semicolon doesn't throw off content assist
	 */
	public void testContentAssistStructModuleInputModuleScope() {
		SVCorePlugin.getDefault().enableDebug(false);

		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} s;\n" +
			"\n" +
			"module foo_m(input s b);\n" +
			"\n" +
			"    b.<<MARK>>\n" +
			"endmodule\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field");
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructInClassTypedef() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"\n" +
			"    typedef struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"    } my_struct_t;\n" +
			"\n" +
			"    my_struct_t              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field");
	}

	public void testContentAssistStructInClassTypedefRedirect() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"\n" +
			"    typedef struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"    } my_struct_t;\n" +
			"\n" +
			"	typedef my_struct_t my_struct_t2;\n" +
			"\n" +
			"    my_struct_t2              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field");
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructField() {
		SVCorePlugin.getDefault().enableDebug(false);

		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"    struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"		 logic [1:0]     my_logic_field;\n" +
			"        logic [2:0]     my_logic_queue[$];\n" +
			"    } my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"my_int_field", "my_bit_field",
				"my_logic_field", "my_logic_queue");
	}

}
