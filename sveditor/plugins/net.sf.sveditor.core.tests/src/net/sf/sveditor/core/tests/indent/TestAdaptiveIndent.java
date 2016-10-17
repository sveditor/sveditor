/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class TestAdaptiveIndent extends TestCase {
	
	public void testAdaptiveSecondLevel() {
		LogHandle log = LogFactory.getLogHandle("testAdaptiveSecondLevel");
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																				// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"		function void foobar();\n" +													// 9
			"a = 5;\n" +
			"	endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																				// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"		function void foobar();\n" +													// 9
			"			a = 5;\n" +
			"		endfunction\n" +
			"\n";
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(9);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testAdaptiveSecondLevel", expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testPostComment() {
		String content =
			"class foo;\n" +					// 1
			"	function void my_func();\n" +		// 2
			"		if (foobar) begin\n" +				// 3
			"		end else begin\n" +				// 4
			"			// comment block\n" +				// 5
			"			a\n"
			;
		String expected =
			"class foo;\n" +					// 1
			"	function void my_func();\n" +		// 2
			"		if (foobar) begin\n" +				// 3
			"		end else begin\n" +				// 4
			"			// comment block\n" +				// 5
			"			a\n"
			;
			
		SVCorePlugin.getDefault().enableDebug(false);
		
		coreAutoIndentTest("testPostComment", content, 5, expected);
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
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testBasicModule");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);

		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(9);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testBasicModule", expected, result);
		LogFactory.removeLogHandle(log);
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

		LogHandle log = LogFactory.getLogHandle("testModuleContainingClass");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);

		indenter.setAdaptiveIndentEnd(6);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testBasicModule", expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testAdaptiveIf() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"			\n" +																			// 8
			"	function void foobar();\n" +															// 9
			"		a = 6;\n" +																			// 10
			"		if (foobar) begin\n" +															// 11
			"a = 5;\n" +
			"end\n" +
			"endfunction\n" +
			"\n";
		String expected =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"	\n" +																					// 8
			"	function void foobar();\n" +															// 9
			"		a = 6;\n" +
			"		if (foobar) begin\n" +															// 11
			"			a = 5;\n" +																	// 12
			"		end\n" +																		// 13
			"	endfunction\n" +																		// 14
			"	\n";
		
		LogHandle log = LogFactory.getLogHandle("testAdaptiveIf");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testAdaptiveIf", expected, result);
		LogFactory.removeLogHandle(log);
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
			"		end\n"
			;
		
		LogHandle log = LogFactory.getLogHandle("testPostSysTfIfPartial");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent(12, 14);
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testPostSysTfIf", expected, result);
		LogFactory.removeLogHandle(log);
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
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"		function void foobar();\n" +														// 9
			"			$psprintf(\"Hello World\\n Testing %d\\n\",\n" +								// 10
			"					a, b, c);\n" +															// 11
			"			if (foobar) begin\n" +															// 12
			"				a = 6;\n" +																	// 13
			"			end\n" +																		// 14
			"		endfunction\n" +
			"\n";
		
		LogHandle log = LogFactory.getLogHandle("testPostSysTfIfFull");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		// indenter.setAdaptiveIndentEnd(11);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testPostSysTfIfFull", expected, result);
		LogFactory.removeLogHandle(log);
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
			"	`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"	\n" +																			// 8
			"		function void foobar();\n" +													// 9
			"			a = 5;\n" +
			"		endfunction\n" +
			"\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testAdaptiveFirstLevelScope");
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(8);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, "testAdaptiveFirstLevelScope", expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testAdaptiveDistCloseBrace() {
		String content =
				"class someclass;\n" +
				"	constraint clock {\n" +
				"		clk_cfg.period dist {\n" +
				"			[1:10  ] :/ 1,\n" +
				"			11       := 1,\n" +
				"			12       := 1,\n" +
				"			[13: 15] :/ 1\n" +
				"};\n" + 
				"clk_cfg.jitter < (3 * 1000);\n" +
				"\n";
		
		String expected =
				"class someclass;\n" +						// 1
				"	constraint clock {\n" +
				"		clk_cfg.period dist {\n" +
				"			[1:10  ] :/ 1,\n" +
				"			11       := 1,\n" +				// 5
				"			12       := 1,\n" +
				"			[13: 15] :/ 1\n" +				// 7
				"		};\n" + 
				"		clk_cfg.jitter < (3 * 1000);\n" +
				"\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(getName());
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(7);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(log, getName() + " - Adaptive", expected, result);

		scanner = new SVIndentScanner(new StringTextScanner(content));
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(false);
		indenter.setAdaptiveIndentEnd(-1);

		result = indenter.indent();
		
		log.debug("Result (Full):");
		log.debug(result);
		IndentComparator.compare(log, getName() + " - Full", expected, result);
		
		LogFactory.removeLogHandle(log);
	}
	
	private void coreAutoIndentTest(
			String testname, 
			String content,
			int adaptive_end,
			String expected) {
		LogHandle log = LogFactory.getLogHandle(testname);
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);

		indenter.setAdaptiveIndentEnd(adaptive_end);

		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		LogFactory.removeLogHandle(log);
	}
	
//	public void test

}
