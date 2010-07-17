package net.sf.sveditor.core.tests.srcgen;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.srcgen.MethodGenerator;

public class TestMethodGenerator extends TestCase {
	
	public void testVoidFunction() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function void foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}

	public void testBuiltinRetFunction() throws SVParseException {
		String content =
			"function longint unsigned foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function longint unsigned foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}
	
	public void testParamClassRetFunction() throws SVParseException {
		String content =
			"function foo_c #(bar_c) foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function foo_c #(bar_c) foobar();\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}

	public void testParamClassParamFunction() throws SVParseException {
		String content =
			"function void foobar(output foo_c #(bar_c) p);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function void foobar(output foo_c #(bar_c) p);\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}

	public void testRefParamFunction() throws SVParseException {
		String content =
			"function void foobar(ref int a);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function void foobar(ref int a);\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}

	public void testRefVarListParamFunction() throws SVParseException {
		String content =
			"function void foobar(ref int a, b, c);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		String exp = 
			"    function void foobar(ref int a, ref int b, ref int c);\n" +
			"\n" +
			"    endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope tf = parser.parsers().functionParser().parse(null, 0);
		
		MethodGenerator gen = new MethodGenerator();
		
		String src = gen.generate(tf);
		
		System.out.println("src:\n" + src);
		
		assertEquals(exp.trim(), src.trim());
	}

}
