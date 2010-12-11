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

import java.io.ByteArrayOutputStream;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class IndentTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndentTests");
		suite.addTest(new TestSuite(IndentTests.class));
		suite.addTest(new TestSuite(NoHangIndentTests.class));
		suite.addTest(new TestSuite(TestIndentScanner.class));
		suite.addTest(new TestSuite(TestAdaptiveIndent.class));
		
		return suite;
	}
	
	public void testClass() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		bos = utils.readBundleFile("/indent/class1.svh");
		
		String ref = bos.toString();
		StringBuilder sb = removeLeadingWS(ref);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(sb));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		StringBuilder result = new StringBuilder(indenter.indent(-1, -1));
		
		IndentComparator.compare("testClass", ref, result.toString());
	}

	public void testBasicClass() {
		String content =
			"\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"function new();\n" +
			"if (foo)\n" +
			"foo = 5;\n" +
			"else if (foo2) begin\n" +
			"foo = 6;\n" +
			"end\n" +
			"endfunction\n" +
			"endclass\n"
			;
		String expected =
			"\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"	function new();\n" +
			"		if (foo)\n" +
			"			foo = 5;\n" +
			"		else if (foo2) begin\n" +
			"			foo = 6;\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicClass", expected, result);
	}
	
	public void testEmptyCaseStmt() throws Exception {
		String content =
			"module t;\n" +
			"logic a;\n" +
			"always @ (a) begin\n" +
			"case(a)\n" + 
			"endcase\n" +
			"end\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	logic a;\n" +
			"	always @ (a) begin\n" +
			"		case(a)\n" + 
			"		endcase\n" +
			"	end\n" +
			"endmodule\n"
			;

		System.out.println("--> testEmptyCaseStmt()");
		SVCorePlugin.getDefault().enableDebug(true);
		try {
			SVIndentScanner scanner = new SVIndentScanner(
					new StringTextScanner(content));

			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			indenter.init(scanner);
			indenter.setTestMode(true);

			String result = indenter.indent();

			System.out.println("Result:");
			System.out.println(result);
			IndentComparator.compare("testBasicClass", expected, result);
		} catch (Exception e) {
			e.printStackTrace();
			throw e;
		} finally {
			System.out.println("<-- testEmptyCaseStmt()");
		}
	}

	public void testInitialBlock() {
		String content =
			"module t;\n" +
			"logic a;\n" +
			"initial begin\n" +
			"a = 5;\n" +
			"end\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	logic a;\n" +
			"	initial begin\n" +
			"		a = 5;\n" +
			"	end\n" +
			"endmodule\n"
			;
		System.out.println("--> testInitialBlock");
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicClass", expected, result);
		System.out.println("<-- testInitialBlock");
	}

	public void testBasicModuleComment() {
		String content =
			"module t; // Comment.\n" +
			"logic a;\n" +
			"logic b;\n" +
			"\n" +
			"endmodule\n" 
			;
		String expected =
			"module t; // Comment.\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"\n" +
			"endmodule\n" 
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicModuleWire", expected, result);
	}
	
	public void testNestedModule() {
		String content =
			"module t;\n" +
			"logic a;\n" +
			"logic b;\n" +
			"\n" +
			"module t1;\n" +
			"wire a;\n" +
			"wire b;\n" +
			"endmodule\n" +
			"endmodule\n" 
			;
		String expected =
			"module t;\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"\n" +
			"	module t1;\n" +
			"		wire a;\n" +
			"		wire b;\n" +
			"	endmodule\n" +
			"endmodule\n" 
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testNestedModule", expected, result);
	}
	
	public void testIndentPostSingleComment() {
		String content =
			"class foo;\n" +					// 1
			"function void my_func();\n" +		// 2
			"if (foobar) begin\n" +				// 3
			"end else begin\n" +				// 4
			"// comment block\n" +				// 5
			"a.b = 5;\n" +						// 6
			"end\n" +							// 7
			"endfunction\n" +					// 8
			"endclass\n" 						// 9
			;
		String expected =
			"class foo;\n" +
			"	function void my_func();\n" +
			"		if (foobar) begin\n" +
			"		end else begin\n" +
			"			// comment block\n" +
			"			a.b = 5;\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n" 
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testIndentPostSingleComment", expected, result);
	}

	public void testBasicModuleWire() {
		String content =
			"module top;\n" +
			"logic a;\n" +
			"logic b;\n" +
			"endmodule\n"
			;
		String expected =
			"module top;\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicModuleWire", expected, result);
	}

	public void testNewLineIf() {
		String content =
			"\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"function new();\n" +
			"if (foo)\n" +
			"foo = 5;\n" +
			"else\n" +
			"if (foo2) begin\n" +
			"foo = 6;\n" +
			"end\n" +
			"endfunction\n" +
			"endclass\n"
			;
		String expected =
			"\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"	function new();\n" +
			"		if (foo)\n" +
			"			foo = 5;\n" +
			"		else\n" +
			"		if (foo2) begin\n" +
			"			foo = 6;\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		System.out.println("Result:");
		System.out.println(result);
		IndentComparator.compare("testBasicClass", expected, result);
	}

	public void testModule() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		bos = utils.readBundleFile("/indent/module.svh");
		
		String expected = bos.toString();
		StringBuilder sb = removeLeadingWS(expected);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(sb));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		IndentComparator.compare("testModule", expected, result);
		
		/*
		StringBuilder result = new StringBuilder(indenter.indent(-1, -1));
		StringBuilder reference = new StringBuilder(ref);
		
		String ref_line, ind_line;
		int err_cnt = 0;
		int pass_cnt = 0;
		
		do {
			ref_line = readLine(reference);
			ind_line = readLine(result);
			
			if (ref_line != null && ind_line != null) {
				if (ref_line.equals(ind_line)) {
					System.out.println("[OK ]:" + ref_line);
					pass_cnt++;
				} else {
					System.out.println("[ERR]:" + ref_line);
					System.out.println("[   ]:" + ind_line);
					err_cnt++;
				}
			}
		} while (ref_line != null && ind_line != null);
		
		assertNull("Checking that output not truncated", ref_line);
		assertNull("Checking for no excess output", ind_line);
		
		assertEquals("Expect no errors", 0, err_cnt);
		assertTrue("Check accomplished work", (pass_cnt != 0));
		 */
	}

	public void testMultiBlankLine() {
		String ref = 
		"class my_component1 extends ovm_component;\n" +
		"	\n" +
		"	\n" +
		"	function new(string name, ovm_component parent);\n" +
		"		super.new(name, parent);\n" +
		"	endfunction\n" +
		"	\n"  +
		"	\n" +
		"endclass\n";
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testMultiBlankLine", ref, result);
	}
	
	public void testFunctionComment() {
		String ref = 
			"class my_class;\n" +
			"\n" +
			"	/**\n" +
			"	 * my_func\n" +
			"	 *\n" +
			"	 */\n" +
			"	function void foobar;\n" +
			"\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n"
			;
			
			SVCorePlugin.getDefault().enableDebug(false);
			
			// Run the indenter over the reference source
			SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			indenter.init(scanner);
			indenter.setTestMode(true);
			
			String result = indenter.indent(-1, -1);
			
			System.out.println("Ref:");
			System.out.print(ref);
			System.out.println("====");
			System.out.println("Result:");
			System.out.print(result);
			System.out.println("====");
			
			IndentComparator.compare("testFunctionComment", ref, result);
	}

	public void testModuleFirstItemComment() {
		String ref = 
		"module foo;\n" +
		"	// this is a comment\n" +
		"	a = 5;\n" +
		"endmodule\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testModuleFirstItemComment", ref, result);
	}

	public void testInitialFirstItemComment() {
		String ref = 
		"module foo;\n" +
		"	\n" +
		"	initial begin\n" +
		"		// this is a comment\n" +
		"	end\n" +
		"	a = 5;\n" +
		"endmodule\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);

		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testInitialFirstItemComment", ref, result);
	}

	public void testFunctionFirstItemComment() {
		String ref = 
		"module foo;\n" +
		"	\n" +
		"	function automatic void foobar_f();\n" +
		"		// this is a comment\n" +
		"	endfunction\n" +
		"	a = 5;\n" +
		"endmodule\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testFunctionFirstItemComment", ref, result);
	}

	public void testIfInFunction() {
		String ref =
		"class xbus_bus_monitor;\n" +							// 1
		"\n" +													// 2
		"		function void ignored();\n" +					// 3
		"		endfunction\n" +								// 4
		"\n" +													// 5
		"		// perform_transfer_coverage\n" +				// 6
		"		function void perform_transfer_coverage();\n" +
		"			if (trans_collected.read_write != NOP) begin\n" +
		"				-> cov_transaction;\n" +
		"				for (int unsigned i = 0; i < trans_collected.size; i++) begin\n" +
        "					addr = trans_collected.addr + i;\n" +
        "					data = trans_collected.data[i];\n" +
        "					wait_state = trans_collected.wait_state[i];\n" +
        "					-> cov_transaction_beat;\n" +
        "				end\n" +
        "			end\n" +
        "		endfunction : perform_transfer_coverage\n" +
        "\n" +
        "endclass : xbus_bus_monitor\n"
        ;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testIfInFunction", ref, result);
	}

	private StringBuilder removeLeadingWS(String ref) {
		StringBuilder sb = new StringBuilder();
		int i=0;
		while (i < ref.length()) {
			// Read leading whitespace
			while (i < ref.length() && 
					Character.isWhitespace(ref.charAt(i)) &&
					ref.charAt(i) != '\n') {
				i++;
			}
			
			if (i >= ref.length()) {
				break;
			}
			
			if (ref.charAt(i) == '\n') {
				sb.append('\n');
				i++;
				continue;
			} else {
				// Read to the end of the line
				while (i < ref.length() && ref.charAt(i) != '\n') {
					sb.append(ref.charAt(i));
					i++;
				}
				
				if (i < ref.charAt(i)) {
					sb.append('\n');
				}
			}
		}
		
		return sb;
	}

	/*
	private String readLine(StringBuilder sb) {
		int end = 0;
		String ret = null;
		
		while (end < sb.length() && sb.charAt(end) != '\n') {
			end++;
		}
		
		if (end < sb.length()) {
			if (end == 0) {
				ret = "";
				sb.delete(0, 1);
			} else {
				ret = sb.substring(0, end);
				sb.delete(0, end+1);
			}
		}
		
		return ret;
	}
	 */

}
