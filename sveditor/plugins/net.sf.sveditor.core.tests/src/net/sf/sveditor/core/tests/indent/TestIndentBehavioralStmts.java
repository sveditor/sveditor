/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.indent;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndentBehavioralStmts extends SVCoreTestCaseBase {

	public void testNewLineIf() {
		String expected =
			"\n" +
			"//comment0\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"	//comment1\n" +
			"	function new();\n" +
			"		//comment2\n" +
			"		if (foo)\n" +
			"			//comment3\n" +
			"			foo = 5;\n" +
			"		//comment4\n" +
			"		else\n" +
			"		if (foo2) begin\n" +
			"			//comment6\n" +
			"			foo = 6;\n" +
			"			//comment7\n" +
			"		end\n" +
			"		//comment8\n" +
			"	endfunction\n" +
			"	//comment9\n" +
			"endclass\n" +
			"//comment10\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, expected);
	}

	public void testAssertRandomizeWith() {
		String ref =
		"class foo;\n" +
		"	virtual function void build_phase(uvm_phase phase);\n" +
		"		assert(this.randomize(random_int) with\n" +
		"				{ random_int > 0;\n" +
		"					random_int<100;\n" +
		"				});\n" +
		"		assert(this.randomize(random_int) with\n" +
		"				{ random_int > 0;\n" +
		"					random_int<100;\n" +
		"				});\n" +
		"	endfunction\n" +
		"endclass\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, ref);
	}
	
	public void testAssertRandomizeWith_2() {
		String expected =
				"class someclass;\n" +
				"	function void my_func;\n" +
				"		my_class cls1; \n" +
				"		assert(cls1.randomize() with {\n" +
				"				cls1.a == 2;\n" +
				"			})\n" +
				"		else $display (\"ERROR\");\n" +
				"	endfunction\n" +
				"endclass\n"
				;		
		
		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, expected);
	}
	
}
