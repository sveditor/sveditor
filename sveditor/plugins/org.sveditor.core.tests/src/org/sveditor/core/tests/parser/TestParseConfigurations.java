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
package org.sveditor.core.tests.parser;

import org.sveditor.core.SVCorePlugin;

import junit.framework.TestCase;

public class TestParseConfigurations extends TestCase {
	
	public void testConfig_33_2_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testConfig_33_2_1";
		String content =
			"config cfg1; // specify rtl adder for top.a1, gate-level adder for top.a2\n" +
			"	design rtlLib.top;\n" +
			"	default liblist rtlLib;\n" +
			"	instance top.a2 liblist gateLib;\n" +
			"endconfig\n" 
			;
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"cfg1"});
	}
	
	public void testConfig_33_2_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testConfig_33_2_2";
		String content =
			"config cfg2;\n" +
			"	localparam S = 24;\n" +
			"	design rtlLib.top4;\n" +
			"	instance top4.a1 use #(.W(top4.S));\n" +
			"	instance top4.a2 use #(.W(S));\n" +
			"endconfig\n"
			;
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"cfg2"});
	}

}
