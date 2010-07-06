package net.sf.sveditor.core.tests.indent;

import junit.framework.TestCase;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
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
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"	a = 5;\n" +
			"endfunction\n" +
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(9);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		assertEquals("Expected indent", expected, result);
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
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"	a = 6;\n" +
			"		if (foobar) begin\n" +															// 11
			"			a = 5;\n" +																	// 12
			"		end\n" +																		// 13
			"endfunction\n" +																		// 14
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		assertEquals("Expected indent", expected, result);
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
		
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(8);

		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		assertEquals("Expected indent", expected, result);
	}

}
