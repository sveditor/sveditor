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
package net.sf.sveditor.core.tests.hierarchy;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestModuleHierarchy extends SVCoreTestCaseBase {

	public void testModuleSubHierarchy() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m1;\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" +
			"	m1 m1_1();\n" +
			"	m1 m1_2();\n" +
			"endmodule\n" +
			"\n" +
			"module m3;\n" +
			"	m2 m2_1();\n" +
			"	m2 m2_2();\n" +
			"endmodule\n" +
			"\n" +
			"module top;\n" +
			"	m3 m3_1();\n" +
			"	m3 m3_2();\n" +
			"	m3 m3_3();\n" +
			"endmodule\n" +
			"\n"
			;
		String testname = "testModuleSubHierarchy";
		
		HierarchyTests.runModuleHierarchyTest(testname, doc, "top", fCacheFactory,
				"top.m3_1.m2_2.m1_1");
	}
}
