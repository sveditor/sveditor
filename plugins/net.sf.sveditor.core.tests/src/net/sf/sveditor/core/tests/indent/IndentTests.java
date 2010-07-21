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
import net.sf.sveditor.core.indent.SVDefaultIndenter;
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
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		StringBuilder result = new StringBuilder(indenter.indent(-1, -1));
		StringBuilder reference = new StringBuilder(ref);
		
		/*
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
		IndentComparator.compare("testClass", ref, result.toString());
	}
	
	public void testModule() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		bos = utils.readBundleFile("/indent/module.svh");
		
		String ref = bos.toString();
		StringBuilder sb = removeLeadingWS(ref);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(sb));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
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
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		String result = indenter.indent(-1, -1);
		
		System.out.println("Ref:");
		System.out.print(ref);
		System.out.println("====");
		System.out.println("Result:");
		System.out.print(result);
		System.out.println("====");
		
		IndentComparator.compare("testMultiBlankLine", ref, result);
	}

	public void testModuleFirstItemComment() {
		String ref = 
		"module foo;\n" +
		"	// this is a comment\n" +
		"	a = 5;\n" +
		"endmodule\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
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
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
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
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
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
		"	function void ignored();\n" +						// 3
		"	endfunction\n" +									// 4
		"\n" +													// 5
		"	// perform_transfer_coverage\n" +					// 6
		"	function void perform_transfer_coverage();\n" +
		"		if (trans_collected.read_write != NOP) begin\n" +
		"			-> cov_transaction;\n" +
		"			for (int unsigned i = 0; i < trans_collected.size; i++) begin\n" +
        "				addr = trans_collected.addr + i;\n" +
        "				data = trans_collected.data[i];\n" +
        "				wait_state = trans_collected.wait_state[i];\n" +
        "				-> cov_transaction_beat;\n" +
        "			end\n" +
        "		end\n" +
        "	endfunction : perform_transfer_coverage\n" +
        "\n" +
        "endclass : xbus_bus_monitor\n"
        ;
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(-1);
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
	

}
