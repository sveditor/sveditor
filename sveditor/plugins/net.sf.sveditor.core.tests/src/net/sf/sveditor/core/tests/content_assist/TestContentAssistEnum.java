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


package net.sf.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistEnum extends SVCoreTestCaseBase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistEnumeratorAssign() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef enum {\n" +
			"    E_ENUM_A,\n" +
			"    E_ENUM_B,\n" +
			"    _MY_ENUM_C\n" +
			"} my_enum_t;\n" +
			"\n" +
			"class my_class;\n" +
			"    my_enum_t              ab;\n" +
			"\n" +
			"    function void foo();\n" +
			"        ab = E_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"E_ENUM_A", "E_ENUM_B");
	}

	public void testContentAssistPkgEnumeratorAssign() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"package pkg;\n" +
			"typedef enum {\n" +
			"    E_ENUM_A,\n" +
			"    E_ENUM_B,\n" +
			"    _MY_ENUM_C\n" +
			"} my_enum_t;\n" +
			"\n" +
			"endpackage\n" +
			"\n" +
			"class my_class;\n" +
			"    my_enum_t              ab;\n" +
			"\n" +
			"    function void foo();\n" +
			"        ab = E_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"E_ENUM_A", "E_ENUM_B");
	}
	
	public void testContentAssistInClassEnumDecl() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class my_class;\n" +
			"	typedef enum {\n" +
			"		E_ENUM_A,\n" +
			"		E_ENUM_B,\n" +
			"		_MY_ENUM_C\n" +
			"	} my_enum_t;\n" +
			"    my_enum_t              ab;\n" +
			"\n" +
			"    function void foo();\n" +
			"        ab = E_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"E_ENUM_A", "E_ENUM_B");
	}
	
}
