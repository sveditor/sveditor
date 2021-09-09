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


package org.sveditor.core.tests.content_assist;

import org.sveditor.core.SVCorePlugin;

import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestParamClassContentAssist extends SVCoreTestCaseBase {
	
	/**
	 * Placeholder, since a test class cannot be empty
	 */
	public void testNullTest() {
		
	}

	public void EXP_FAIL_testParameterizedField() {
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class container_t #(T=int);\n" +
			"    T            m_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"       container_t #(elem_t)  cont;\n" +
			"\n" +
			"    function void my_func();\n" +
			"        cont.m_field.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(this, doc, "my_field");
	}

	public void EXP_FAIL_testParameterizedFunction() {
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class container_t #(T=int);\n" +
			"    T            m_field;\n" +
			"    function T get_element();\n" +
			"        return m_field;\n" +
			"    endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"       container_t #(elem_t)  cont;\n" +
			"\n" +
			"    function void my_func();\n" +
			"        cont.get_element().<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(this, doc, "my_field");
	}

}
