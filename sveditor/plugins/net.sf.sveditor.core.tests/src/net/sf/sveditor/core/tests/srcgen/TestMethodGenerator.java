/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.srcgen;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.srcgen.MethodGenerator;
import net.sf.sveditor.core.tests.indent.IndentComparator;

public class TestMethodGenerator extends TestCase {
	
	private SVDBTask parse_tf(String content, String name) throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), name);
		
		parser.parsers().taskFuncParser().parse(scope, null, 0);

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
			"     * foobar()\n" +
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
			"     * foobar()\n" +
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
		String content =
			"function foo_c #(bar_c) foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    /**\n" +
			"     * foobar()\n" +
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
			"     * foobar()\n" +
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
			"     * foobar()\n" +
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
			"     * foobar()\n" +
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
			"     * foobar()\n" +
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
}
