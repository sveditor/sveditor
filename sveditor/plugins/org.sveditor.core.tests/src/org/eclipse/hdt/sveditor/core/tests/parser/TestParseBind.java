/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;

public class TestParseBind extends TestCase {
	
	public void testBasicBind() throws SVParseException {
		String testname = "testBasicBind";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind target_scope monitor m1(.a, .b, .c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"m1"});
	}

	public void testHierarchicalBind() throws SVParseException {
		String testname = "testHierarchicalBind";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind target_scope.subscope monitor m1(.a, .b, .c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"m1"});
	}

	public void testTypedHierarchicalBind() throws SVParseException {
		String testname = "testHierarchicalBind";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind cpu: target_scope.subscope monitor m1(.a, .b, .c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"m1"});
	}

	public void testLRMEx1() throws SVParseException {
		String testname = "testLRMEx1";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind cpu: cpu1 fpu_props fpu_rules_1(a, b, c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"fpu_rules_1"});
	}

	public void testLRMEx2() throws SVParseException {
		String testname = "testLRMEx2";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module t;\n" +
			"	bind cpu: cpu1, cpu2, cpu3 fpu_props fpu_rules_1(a, b, c);\n" +
			"endmodule\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"fpu_rules_1"});
	}

}
