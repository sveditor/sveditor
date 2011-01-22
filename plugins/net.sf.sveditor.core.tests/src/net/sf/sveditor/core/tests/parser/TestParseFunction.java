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


package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;

public class TestParseFunction extends TestCase {
	
	public void testBasicFunction() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		parser.parsers().functionParser().parse(null, 0);
	}

	public void testReturnOnlyFunction() throws SVParseException {
		String content =
			"class foobar;\n" +
			"local virtual function string foobar();\n" +
			"    return \"foobar\";\n" +
			"endfunction\n" +
			"endclass\n" 
			;
		
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		try {
			parser.parsers().classParser().parse(0);
		} catch (SVParseException e) {
			e.printStackTrace();
			throw e;
		}
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalVarsWithCast() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    int a = integer'(5);\n" +
			"    int b = longint'(6);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope func = parser.parsers().functionParser().parse(null, 0);

		assertEquals(2, func.getItems().size());
		assertEquals("a", SVDBItem.getName(func.getItems().get(0)));
		assertEquals("b", SVDBItem.getName(func.getItems().get(1)));
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalTimeVar() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    time t = 10ns;\n" +
			"    t = 20ns;\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope func = parser.parsers().functionParser().parse(null, 0);

		assertEquals(1, func.getItems().size());
		assertEquals("t", SVDBItem.getName(func.getItems().get(0)));
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalTypedef() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    typedef foo #(BAR) foo_t;\n" +
			"    foo_t              a;\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope func = parser.parsers().functionParser().parse(null, 0);

		assertEquals(2, func.getItems().size());
		assertEquals("foo_t", SVDBItem.getName(func.getItems().get(0)));
		assertEquals("a", SVDBItem.getName(func.getItems().get(1)));
	}

	public void testStaticFunction() throws SVParseException {
		String content =
			"function static void foobar();\n" +
			"    int a;\n" +
			// "    a = 5;\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
//		SVDBTaskFuncScope func = 
			parser.parsers().functionParser().parse(null, 0);
	}
	
	public void testIfElseBody() throws SVParseException {
		String content =
			"function new();\n" +
			"    string ini_file;\n" +
			"\n" +
		    "    if ($value$plusargs(\"INFACT_AXI_FULL_PROTOCOL_INI=%s\", ini_file)) begin\n" +
			"        ovm_report_info(\"INFACT_AXI_FULL_PROTOCOL\",\n" + 
			"            {\"Loading parameters from .ini file \", ini_file});\n" +
			"        load_ini(ini_file);\n" +
			"    end else begin\n" +
			"        ovm_report_info(\"INFACT_AXI_FULL_PROTOCOL\",\n" + 
			"            {\"No .ini file specified\"});\n" +
			"    end\n" +
			"endfunction\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
//		SVDBTaskFuncScope func = 
			parser.parsers().functionParser().parse(null, 0);
	}

	public void testAutomaticFunction() throws SVParseException {
		String content =
			"function automatic void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		parser.parsers().functionParser().parse(null, 0);
	}

	public void testParamListFunction() throws SVParseException {
		String content =
			"function automatic void foobar(\n" +
			"        input int foobar,\n" +
			"        ref object bar,\n" +
			"        int foo);\n" +
			"    a_type foo, bar;\n" +
			"    b_type foo_q[$];\n" +
			"    b_cls #(foobar, bar) elem;\n" +
			"    int i, j, k;\n" +
			"    for (int i=0; i<5; i++) begin\n" +
			"        a = 5;\n" +
			"    end\n" +
			"endfunction\n";
		
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBTaskFuncScope func = parser.parsers().functionParser().parse(null, 0);
		
		assertEquals("bar", func.getParams().get(1).getName());
		assertEquals(SVDBParamPort.Direction_Ref,
				func.getParams().get(1).getDir());
	}

}
