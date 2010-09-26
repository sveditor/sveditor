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
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.srcgen.MethodGenerator;
import net.sf.sveditor.core.tests.indent.IndentComparator;

public class TestMethodGenerator extends TestCase {
	
	public void testVoidFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testVoidFunction", exp, src);
	}

	public void testBuiltinRetFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testBuiltinRetFunction", exp, src);
	}
	
	public void testParamClassRetFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testParamClassRetFunction", exp, src);
	}

	public void testParamClassParamFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testParamClassParamFunction", exp, src);
	}

	public void testRefParamFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testRefParamFunction", exp, src);
	}

	public void testRefVarListParamFunction() throws SVParseException {
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
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		IndentComparator.compare("testRefVarListParamFunction", exp, src);
	}

}
