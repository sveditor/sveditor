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
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndentCovergroup extends SVCoreTestCaseBase {

	// Seems the concatenation in the cp_3 coverpoint throws off the indenter
	public void disabled_testCovergroup() {
		String expected =
				"class foobar;\n" +
				"	\n" +
				"	covergroup foobar;\n" +
				"		\n" +
				"		var_cp : coverpoint (var) iff (var_cond);\n" +
				"		var1_cp : coverpoint (var) iff (var_cond);\n" +
				"		var2_cp : coverpoint (var) iff (var_cond) {\n" +
				"			bins subrange1[] = {[0:3]};\n" +
				"			bins subrange2[] = {\n" +
				"				[0:3],\n" +
				"				[4:7]\n" +
				"			};\n" +
				"		}\n" +
				"	endgroup\n" +
				"	covergroup cg_1;\n" +
				"		cp_3: coverpoint \n" +
				"			{\n" +
				"				top.bit1,\n" +
				"				top.bit2\n" +
				"			} {\n" +
				"				wildcard bins bin_0 = {2'b?0};\n" +
				"				wildcard bins bin_1 = {2'b?1};\n" +
				"			}\n" +
				"	endgroup\n" +
				"endclass\n";		

		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, expected);
	}

	//This test multi-line statements
	public void testLabeledCovergroup() {
		String doc = 
				"class cov_subscriber extends uvm_subscriber;\n" +
				"	covergroup CG_KEYCONTROL_VALUE with function sample(logic [2:0] keycontrol_3bits_for_key_number=0);\n" +
				"		option.per_instance = 1;\n" +
				"	endgroup : CG_KEYCONTROL_VALUE\n" +
				"\n" +
				"	function new(string name, uvm_component parent);\n" +
				"		super.new(name, parent);\n" +
				"	endfunction\n" +
				"endclass\n" +
				"\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		IndentTests.runTest(getName(), fLog, doc);
	}
}
