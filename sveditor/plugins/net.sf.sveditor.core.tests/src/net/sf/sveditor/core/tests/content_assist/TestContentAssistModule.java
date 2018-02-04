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

		ContentAssistTests.runTest(this, doc, true, false,
				"a", "b", "m", "d",
				"process", "semaphore");
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

		ContentAssistTests.runTest(this, doc, 
				"AA");		
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

		ContentAssistTests.runTest(this, doc, 
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

		ContentAssistTests.runTest(this, doc, 
				"MY_PARAM_A", "MY_PARAM_B");
	}
}


