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


package org.eclipse.hdt.sveditor.core.tests.srcgen;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.parser.SVParser;
import org.eclipse.hdt.sveditor.core.srcgen.MethodGenerator;

import junit.framework.TestCase;
import org.eclipse.hdt.sveditor.core.tests.indent.IndentComparator;

public class TestMethodGenerator extends TestCase {
	
	private SVDBTask parse_tf(String content, String name) throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		SVParser parser = new SVParser();
		parser.init(new StringInputStream(content), name);
		
		parser.parsers().taskFuncParser().parse(scope, -1, 0);

		return (SVDBTask)scope.getChildren().iterator().next();
	}
	
	public void testVoidFunction() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testVoidFunction");
		String content =
			"function void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testVoidFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, "testVoidFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testBuiltinRetFunction() throws SVParseException {
		LogHandle log = LogFactory.getLogHandle("testBuiltinRetFunction");
		String content =
			"function longint unsigned foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function longint unsigned foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testBuiltinRetFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, "testBuiltinRetFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}
	
	public void testParamClassRetFunction() throws SVParseException {
		LogHandle log = LogFactory.getLogHandle("testParamClassRetFunction");
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"function foo_c #(bar_c) foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function foo_c #(bar_c) foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testParamClassRetFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare("testParamClassRetFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testParamClassParamFunction() throws SVParseException {
		LogHandle log = LogFactory.getLogHandle("testParamClassParamFunction");
		String content =
			"function void foobar(output foo_c #(bar_c) p);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(output foo_c #(bar_c) p);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testParamClassParamFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, "testParamClassParamFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testRefParamFunction() throws SVParseException {
		LogHandle log = LogFactory.getLogHandle("testRefParamFunction");
		String content =
			"function void foobar(ref int a);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(ref int a);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testRefParamFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, "testRefParamFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testRefVarListParamFunction() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testRefVarListParamFunction");
		String content =
			"function void foobar(ref int a, b, c);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(ref int a, ref int b, ref int c);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, "testRefVarListParamFunction");
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, "testRefVarListParamFunction", exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testBitVecParamFunction() throws SVParseException {
		String testname = "testBitVecParamFunction";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"function void foobar(bit[31:0] a);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(input bit[31:0] a);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, testname);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, testname, exp, src);
		LogFactory.removeLogHandle(log);
	}
	
	public void testVectoredParam_1() throws SVParseException {
		String testname = "testVectoredParam_1";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"function void foobar(bit[31:0] a[]);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(input bit[31:0] a[]);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, testname);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, testname, exp, src);
		LogFactory.removeLogHandle(log);
	}

	public void testVectoredParam_2() throws SVParseException {
		String testname = "testVectoredParam_2";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"function void foobar(bit[31:0] a[$]);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(input bit[31:0] a[$]);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, testname);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, testname, exp, src);
		LogFactory.removeLogHandle(log);
	}
	
	public void testVectoredParam_3() throws SVParseException {
		String testname = "testVectoredParam_3";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"function void foobar(bit[31:0] a[4]);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(input bit[31:0] a[4]);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, testname);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, testname, exp, src);
		LogFactory.removeLogHandle(log);
	}	
	
	public void testVectoredParam_4() throws SVParseException {
		String testname = "testVectoredParam_4";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"function void foobar(bit[31:0] a[string]);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * Function: foobar\n" +
			"     *\n" +
			"     * Override from class \n" +
			"     */\n" +
			"    function void foobar(input bit[31:0] a[string]);\n" +
			"\n" +
			"    endfunction\n";
		
		SVDBTask tf = parse_tf(content, testname);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		log.debug("src:\n" + src);
		
		IndentComparator.compare(log, testname, exp, src);
		LogFactory.removeLogHandle(log);
	}	
}
