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

public class TestContentAssistModule extends SVCoreTestCaseBase {
	
	
	public void testModuleBlankItems() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m(a, b);\n" +
			"    \n" +
			"<<MARK>>	\n" +
			"	c d(a, b);\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"a", "b", "m", "d");
	}
	
	public void testModuleHierarchyRef_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"`define TOP top\n" +
			"module sub2;\n" +
			"	wire AA;\n" +
			"	wire BA;\n" +
			"endmodule\n" +
			"\n" +
			"module sub1;\n" +
			"	sub2	s2_1();\n" +
			"	sub2	s2_2();\n" +
			"endmodule\n" +
			"\n" +
			"module top;\n" +
			"	sub1	s1_1();\n" +
			"	sub1	s1_2();\n" +
			"endmodule\n" +
			"\n" +
			"module m();\n" +
			"    \n" +
			"	initial begin\n" +
			"		`TOP.s1_1.s2_1.A<<MARK>>\n" +
			"	end\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AA");		
	}

	public void testModuleInstance() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module sub_module1 (\n" +
				"	input logic  a,\n" +
				"	output logic b\n" +
				");\n" +
				"endmodule\n" +
				"\n" +
				"module sub_module2 (\n" +
				"	input logic  a,\n" +
				"	output logic b\n" +
				");\n" +
				"endmodule\n" +
				"\n" +
				"module m();\n" +
				"    \n" +
				"	initial begin\n" +
				"		sub_<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"sub_module1", "sub_module2");		
	}
	
	public void testModuleParameters() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m #(\n" +
			"	parameter MY_PARAM_A = 1,\n" +
			"	parameter MY_PARAM_B = 2\n" +
			"	) (a, b);\n" +
			"    \n" +
			"	initial begin\n" +
			"		int a;\n" +
			"		a = MY_<<MARK>>\n" +
			"	end\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"MY_PARAM_A", "MY_PARAM_B");
	}

	public void testModuleParameters_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m #(\n" +
			"	parameter int MY_PARAM_A = 1,\n" +
			"	parameter int MY_PARAM_B = 2\n" +
			"	) (a, b);\n" +
			"    \n" +
			"	initial begin\n" +
			"		int a;\n" +
			"		$display(\"MY_PARAM_A=%0d\", MY_<<MARK>>\n" +
			"	end\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"MY_PARAM_A", "MY_PARAM_B");
	}
}


