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


package net.sf.sveditor.core.tests.indent;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class TestAdaptiveIndent extends TestCase {
	
	public void testAdaptiveSecondLevel() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"a = 5;\n" +
			"	endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"\n" +																					// 8
			"function void foobar();\n" +															// 9
			"	a = 5;\n" +
			"endfunction\n" +
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(9);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testAdaptiveSecondLevel", expected, result);
	}

	public void testBasicModule() {
		String content =
			"module foo(\n" +	// 1
			" input a,\n" +	// 2
			" int b)\n" +			// 3
			"	;\n" +			// 4
			"	\n" +			// 5
			"  int a;\n" +		// 6
			"	\n" +			// 7
			"	// comment 2\n" +		// 8
			"  initial begin\n" +		// 9
			"a = 5;\n" +
			"end\n" +
			"\n" +
			"endmodule\n";
		
		String expected =
			"module foo(\n" +
			" input a,\n" +
			" int b)\n" +
			"	;\n" +
			"	\n" +
			"  int a;\n" +
			"	\n" +
			"  // comment 2\n" +
			"  initial begin\n" +
			"  	a = 5;\n" +
			"  end\n" +
			"  \n" +
			"endmodule\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);

		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(9);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicModule", expected, result);
	}

	public void testModuleContainingClass() {
		String content =
			"module foo(\n" +	// 1
			" input a,\n" +		// 2
			" int b)\n" +		// 3
			"	;\n" +			// 4
			"	\n" +			// 5
			"  class foo;\n" +  // 6
			"  int a;\n" +		// 7
			"endclass\n" +		// 8
			"	\n" +			// 9
			"endmodule\n";
		
		String expected =
			"module foo(\n" +	// 1
			" input a,\n" +		// 2
			" int b)\n" +		// 3
			"	;\n" +			// 4
			"	\n" +			// 5
			"  class foo;\n" +  // 6
			"  	int a;\n" +		// 7
			"  endclass\n" +	// 8
			"	\n" +			// 9
			"endmodule\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);

		indenter.setAdaptiveIndentEnd(6);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicModule", expected, result);
	}

	public void testAdaptiveIf() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"	a = 6;\n" +																			// 10
			"		if (foobar) begin\n" +															// 11
			"a = 5;\n" +
			"end\n" +
			"	endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"\n" +																					// 8
			"function void foobar();\n" +															// 9
			"	a = 6;\n" +
			"		if (foobar) begin\n" +															// 11
			"			a = 5;\n" +																	// 12
			"		end\n" +																		// 13
			"endfunction\n" +																		// 14
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testAdaptiveIf", expected, result);
	}

	public void testPostSysTfIfPartial() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"	function void foobar();\n" +														// 9
			"		$psprintf(\"Hello World\\n Testing %d\\n\",\n" +								// 10
			"			a, b, c);\n" +																// 11
			"if (foobar) begin\n" +																	// 12
			"a = 6;\n" +																			// 13
			"end\n" +																				// 14
			"  endfunction\n" +
			"\n";
		String expected =
			"		if (foobar) begin\n" +															// 12
			"			a = 6;\n" +
			"		end\n" +
			"\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent(12, 14);
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testPostSysTfIf", expected, result);
	}
	
	public void testPostSysTfIfFull() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"	function void foobar();\n" +														// 9
			"		$psprintf(\"Hello World\\n Testing %d\\n\",\n" +								// 10
			"			a, b, c);\n" +																// 11
			"if (foobar) begin\n" +																	// 12
			"a = 6;\n" +																			// 13
			"end\n" +																				// 14
			"  endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"	function void foobar();\n" +														// 9
			"		$psprintf(\"Hello World\\n Testing %d\\n\",\n" +								// 10
			"			a, b, c);\n" +																// 11
			"		if (foobar) begin\n" +															// 12
			"			a = 6;\n" +																	// 13
			"		end\n" +																		// 14
			"	endfunction\n" +
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		// indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testPostSysTfIfFull", expected, result);
	}
	

	public void testAdaptiveFirstLevelScope() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"a = 5;\n" +
			"	endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"		function void foobar();\n" +													// 9
			"			a = 5;\n" +
			"		endfunction\n" +
			"\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(8);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testAdaptiveFirstLevelScope", expected, result);
	}
	
//	public void test

}
