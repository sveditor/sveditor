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


package net.sf.sveditor.ui.tests.editor;

import org.eclipse.jface.text.BadLocationException;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.SVDefaultIndenter2;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.indent.IndentComparator;
import net.sf.sveditor.core.tests.indent.IndentTests;
import net.sf.sveditor.ui.tests.UiReleaseTests;
import net.sf.sveditor.ui.tests.utils.editor.AutoEditTester;

public class TestAutoIndent extends SVCoreTestCaseBase {
	
	public void testBasicIndent() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		
		tester.type("\n\n");
		tester.type("class foobar;\n");
		tester.type("\nfunction void foobar();\n");
		tester.type("a = 5;\n");
		tester.type("endfunction\n\n");
		tester.type("endclass\n");
		
		String content = tester.getContent();
		
		String expected = 
			"\n\n" +
			"class foobar;\n" +
			"\t\n" +
			"\tfunction void foobar();\n" +
			"\t\ta = 5;\n" +
			"\tendfunction\n" +
			"\t\n" +
			"endclass\n";
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare("testBasicIndent", expected, content);
	}

	public void testPreProc_1() throws BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		
		tester.type("\n");
		tester.type("package foo;\n");
		tester.type("`ifdef FOO\n");
		tester.type("int a;\n");
		tester.type("int b;\n");
		
		String content = tester.getContent();
		
		String expected = 
			"\n" +
			"package foo;\n" +
			"\t`ifdef FOO\n" +
			"\t\tint a;\n" +
			"\t\tint b;\n"
			;
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare(getName(), expected, content);
	}
	
	public void testNoBlockIf() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		SVCorePlugin.getDefault().enableDebug(false);
		
		tester.type("\n\n");
		tester.type("class foobar;\n");
		tester.type("\nfunction void foobar();\n");
		tester.type("if (foo)\n");
		tester.type("$display(\"Hello\");\n");
		tester.type("else\n");
		tester.type("$display(\"Goodbye\");\n");
		tester.type("$display(\"World\");\n");
		tester.type("endfunction\n\n");
		tester.type("endclass\n");
		
		String content = tester.getContent();
		
		String expected = 
			"\n\n" +
			"class foobar;\n" +
			"\t\n" +
			"\tfunction void foobar();\n" +
			"\t\tif (foo)\n" +
			"\t\t\t$display(\"Hello\");\n" +
			"\t\telse\n" +
			"\t\t\t$display(\"Goodbye\");\n" +
			"\t\t$display(\"World\");\n" +
			"\tendfunction\n" +
			"\t\n" +
			"endclass\n";
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare(getName(), expected, content);
	}

	public void testNoBlockIf_2() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		SVCorePlugin.getDefault().enableDebug(false);
		
		tester.type("\n\n");
		tester.type("class foobar;\n");
		tester.type("\nfunction void foobar();\n");
		tester.type("if (foo)\n");
		tester.type("a=5;\n"); 
		tester.type("else\n");
		tester.type("b=6;\n"); 
		tester.type("c=7;\n"); 
		tester.type("endfunction\n\n");
		tester.type("endclass\n");
		
		String content = tester.getContent();
		
		String expected = 
			"\n\n" +
			"class foobar;\n" +
			"\t\n" +
			"\tfunction void foobar();\n" +
			"\t\tif (foo)\n" +
			"\t\t\ta=5;\n" +
			"\t\telse\n" +
			"\t\t\tb=6;\n" +
			"\t\tc=7;\n" +
			"\tendfunction\n" +
			"\t\n" +
			"endclass\n";
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare(getName(), expected, content);
	}
	
	public void testAutoIndentAlways() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		String content = 
			"module foo;\n" +
			"always @(posedge clk) begin\n" +
			"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"end\n" +
			"always @(posedge clk)\n" +
			"begin\n" +
			"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"end\n" +
			"always @(posedge clk)\n" +
			"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"endmodule\n"
			;
		// Type & then paste, to make sure that what we type, and what we get are identical!
		tester.type(content);
		tester.paste(content);
		
		String result = tester.getContent();
		
		String expected = 
			"module foo;\n" +
			"	always @(posedge clk) begin\n" +
			"		if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"		else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"	end\n" +
			"	always @(posedge clk)\n" +
			"	begin\n" +
			"		if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"		else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"	end\n" +
			"	always @(posedge clk)\n" +
			"		if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
			"		else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"		else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
			"endmodule\n"
			;
		
		fLog.debug("Result:\n" + result);
		// Note that we are expecting expected twice, proving that the formatting when we type, is identical
		// to the result when we paste
		IndentComparator.compare("testAutoIndentAlways", expected+expected, result);
	}
	
	public void testAutoIndentInitial() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		String content = 
				"module foo;\n" +
						"initial begin\n" +
						"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"end\n" +
						"initial\n" +
						"begin\n" +
						"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"end\n" +
						"initial\n" +
						"@(posedge bob) begin\n" +
						"if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"end\n" +
						"endmodule\n"
						;
		// Type & then paste, to make sure that what we type, and what we get are identical!
		tester.type(content);
		tester.paste(content);
		
		String result = tester.getContent();
		
		String expected = 
				"module foo;\n" +
						"	initial begin\n" +
						"		if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"		else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"		else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"		else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"	end\n" +
						"	initial\n" +
						"	begin\n" +
						"		if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"		else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"		else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"		else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"	end\n" +
						"	initial\n" +
						"		@(posedge bob) begin\n" +
						"			if (~rst_n_clk) bus_release_cnt <= 'b0;\n" +
						"			else if (slow_packet_finished) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"			else if (|bus_release_cnt) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"			else if(jill) bus_release_cnt <= bus_release_cnt + 1'b1;\n" +
						"		end\n" +
						"endmodule\n"
						;
		
		fLog.debug("Result:\n" + result);
		// Note that we are expecting expected twice, proving that the formatting when we type, is identical
		// to the result when we paste
		IndentComparator.compare("testAutoIndentInitial", expected+expected, result);
	}
	
	public void testGenerateFor() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		String content = 
			"module foo;\n" +
			"generate begin : named_gen\n" +
			"for (i=0; i<5; i++)\n" +
			"begin : named_for\n" +
			"submod sm ();\n" +
			"end\n" +
			"end\n" +
			"endgenerate\n" +
			"generate begin : named_gen\n" +
			"for (i=0; i<5; i++)\n" +
			"begin : named_for\n" +
			"submod sm ();\n" +
			"end\n" +
			"end\n" +
			"endgenerate\n" +
			"endmodule\n"
			;
		// Type & then paste, to make sure that what we type, and what we get are identical!
		tester.type(content);
		tester.paste(content);
		
		String result = tester.getContent();
		
		String expected = 
				"module foo;\n" +
				"	generate begin : named_gen\n" +
				"		for (i=0; i<5; i++)\n" +
				"		begin : named_for\n" +
				"			submod sm ();\n" +
				"		end\n" +
				"	end\n" +
				"	endgenerate\n" +
				"	generate begin : named_gen\n" +
				"		for (i=0; i<5; i++)\n" +
				"		begin : named_for\n" +
				"			submod sm ();\n" +
				"		end\n" +
				"	end\n" +
				"	endgenerate\n" +
				"endmodule\n"
			;
		
		fLog.debug("Result:\n" + result);
		// Note that we are expecting expected twice, proving that the formatting when we type, is identical
		// to the result when we paste
		IndentComparator.compare("testGenerateFor", expected+expected, result);
	}

	public void testAutoPostSingleComment() throws BadLocationException {
		String content =
			"class foo;\n" +
			"function void my_func();\n" +
			"if (foobar) begin\n" +
			"end else begin\n" +
			"// comment block\n" +
			"a.b = 5;\n" +
			"end\n" +
			"endfunction\n" +
			"endclass\n"
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

		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		tester.paste(content);
		
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testAutoPostSingleComment", expected+expected, result);
	}

	public void testPaste() throws BadLocationException {
		String first =
			"`ifndef INCLUDED_transport_packet_svh\n" +
			"`define INCLUDED_transport_packet_svh\n" +
			"\n";
		
		String text = 
			"class vmm_xactor;\n" +
			"\n" +
			"`VMM_NOTIFY notify;\n";
		
		String expected = 
			"`ifndef INCLUDED_transport_packet_svh\n" +
			"	`define INCLUDED_transport_packet_svh\n" +
			"\n" +
			"	class vmm_xactor;\n" +
			"\n" +
			"		`VMM_NOTIFY notify;\n"
			;
			

		SVCorePlugin.getDefault().enableDebug(false);
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(first);
		tester.paste(text);
		
		String content = tester.getContent();
		
		fLog.debug("Result:\n'" + content  + "'\n");
		IndentComparator.compare("testPaste", expected, content);
	}

	/**
	 * Test for 
	 * - #(471) weird copy paste problem
	 * - #(506) Copying multiple lines
	 * 
	 *  This section of the test attempts to check that all variations of multi-line pastes
	 *              Insertion Point                     Pasted Code Properties
	 *            IPSOL  IPLWS   IPIC  IPEOL                PCLWS  PCendCR
	 *  Case1 :   IPSOL                                            PCendCR
	 *  Case2 :          IPLWS                                     PCendCR
	 *  Case3 :                  IPIC                              PCendCR
	 *  Case4 :                        IPEOL                       PCendCR
	 *  Case5 :   IPSOL                                            !PCendCR
	 *  Case6 :          IPLWS                                     !PCendCR
	 *  Case7 :                  IPIC                              !PCendCR
	 *  Case8 :                        IPEOL                       !PCendCR
	 *  Case9 :   IPSOL                                     PCLWS  PCendCR
	 *  Case10:          IPLWS                              PCLWS  PCendCR
	 *  Case11:                  IPIC                       PCLWS  PCendCR
	 *  Case12:                        IPEOL                PCLWS  PCendCR
	 *  Case13:   IPSOL                                     PCLWS  !PCendCR
	 *  Case14:          IPLWS                              PCLWS  !PCendCR
	 *  Case15:                  IPIC                       PCLWS  !PCendCR
	 *  Case16:                        IPEOL                PCLWS  !PCendCR
	 *  
	 *  Legend:
	 *  IPSOL   - Insertion point at start of line
	 *  IPLWS   - Insertion point in leading white space at start of line
	 *  IPIC    - Insertion point in code
	 *  IPEOL   - Insertion point at end of line
	 *  PCLWS   - Pasted code has leading white space
	 *  PCendCR - Pasted code ends with a \n
	 *  
	 * @throws BadLocationException
	 */
	public void testPasteMultiLine() throws BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		String input = 
			"module m(  // Bug 407\n" +
			"		input d\n" +
			"	);\n" +
			"\n" +
			"endmodule\n";
		String expected =
			"module m(  // Bug 407\n" +
			"		input a,\n" +
			"				input b,\n" +
			"		input c,\n" +
			"		input d			,\n" +
			"		input e		\n" +
			"	);\n" +
			"\n" +
			"endmodule\n";
			
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.setContent(input);
		
		// Add input e after end of line.  Note we should keep leading and trailing whitespace
		tester.setCaretOffset("module m(  // Bug 407\n\t\tinput d".length());
		tester.paste("\t\t\t,\ninput e\t\t");

		// Add input c before input d, middle of typed text
		// Expecting the input to be indented
		tester.setCaretOffset("module m(  // Bug 407\n\t\tinput ".length());
		tester.paste("c,\ninput ");

		// Mid-way through start of line, in white space
		tester.setCaretOffset("module m(  // Bug 407\n\t\t".length());
		tester.paste("\t\t\tinput b,\n\t\t\t");

		// Start of line, in white space
		tester.setCaretOffset("module m(  // Bug 407\n".length());
		tester.paste("\t\t\tinput a,\n\t\t\t");
		
		String result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		// Case1 :   IPSOL                                            PCendCR
		//    Insertion point at start of line, paste code ends with CR
		//    Expect pasted code to be indented, no change to lines before or after
		input = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
				"				assign a = 8;\n" +
				"endmodule\n";
		fLog.debug("Input:'\n" + input + "'\n");
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n")
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" +
				"		assign pasted = 1234;   // Case 1\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste("assign pasted = 1234;   // Case 1\n");
		result = tester.getContent();
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case2 :          IPLWS                                     PCendCR
		//    Insertion point in leading whitespace, pasted code ends with CR
		//    Expect pasted code to be indented
		//    Loading white space at insertion point to be removed
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" + 
				"		")
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" +
				"		assign pasted = 1234;   // Case 2\n" +
				// Will remove the leading 2 tabs here as they are "leading whitespace before the 
				// paste-point and will be replaced by the indenter.  The remaining tab will stay
				"	assign a = 6;\n" +		
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste("assign pasted = 1234;   // Case 2\n");
		result = tester.getContent();
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case3 :                  IPIC                              PCendCR
		//    Insertion point in code, pasted code ends with CR
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5" 
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;assign pasted = 1234   // Case 3\n" +
				";\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(";assign pasted = 1234   // Case 3\n");
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case4 :                        IPEOL                       PCendCR
		//    Insertion point in at end of line, pasted code ends with CR
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;assign pasted = 1234;   // Case 4\n" +
				"		assign pasted = 1235;   // Case 4\n" +
				"		\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"assign pasted = 1234;   // Case 4\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case 4\n"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case5 :   IPSOL                                            !PCendCR
		//    Insertion point at start of line, paste code ends with code/ws
		//    Expect pasted code to be indented, no change to lines before or after
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"	assign pasted = 1234;   // Case 5\n" +
				"	assign pasted = 1235;   // Case 5		assign a = 5;\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"assign pasted = 1234;   // Case 5\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case 5"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case6 :          IPLWS                                     !PCendCR
		//    Insertion point in leading whitespace, pasted code ends with code/ws
		//    Expect pasted code to be indented
		//    Loading white space at insertion point to be removed
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" + 
				"\t"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"	assign pasted = 1234;   // Case 6\n" +
				"	assign pasted = 1235;   // Case 6	assign a = 5;\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"assign pasted = 1234;   // Case 6\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case 6"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case7 :                  IPIC                              !PCendCR
		//    Insertion point in code, pasted code ends with code/ws
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5/*				assign pasted = 1234;   // Case 7*/;\n" +
				"		assign pasted = 1235;\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"/*\t\t\t\tassign pasted = 1234;   // Case 7*/;\n" +
				"\t\t\t\t   assign pasted = 1235"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case8 :                        IPEOL                       !PCendCR
		//    Insertion point in at end of line, pasted code ends with code/ws
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;assign pasted = 1234;   // Case 8\n" +
				"		assign pasted = 1235;   // Case 8\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"assign pasted = 1234;   // Case 8\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case 8"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case9 :   IPSOL                                     PCLWS  PCendCR
		//    Insertion point at start of line, paste code leads with whitespace and ends with CR
		//    Expect pasted code to be indented, no change to lines before or after
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n")
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" +
				"		assign pasted = 1234;   // Case 9\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste("				assign pasted = 1234;   // Case 9\n");
		result = tester.getContent();
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case10:          IPLWS                              PCLWS  PCendCR
		//    Insertion point in leading whitespace, pasted code leads with whitespace and ends with CR
		//    Expect pasted code to be indented
		//    Loading white space at insertion point to be removed
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" + 
				"		")
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\n" +
				"		assign pasted = 1234;   // Case 10\n" +
				// Will remove the leading 2 tabs here as they are "leading whitespace before the 
				// paste-point and will be replaced by the indenter.  The remaining tab will stay
				"	assign a = 6;\n" +		
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste("	assign pasted = 1234;   // Case 10\n");
		result = tester.getContent();
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case11:                  IPIC                       PCLWS  PCendCR
		//    Insertion point in code, pasted code leads with whitespace and ends with CR
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5" 
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5		;assign pasted = 1234   // Case11\n" +
				";\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste("		;assign pasted = 1234   // Case11\n");
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case12:                        IPEOL                PCLWS  PCendCR
		//    Insertion point in at end of line, pasted code leads with whitespace and ends with CR
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;\t\t \tassign pasted = 1234;   // Case 12\n" +
				"		assign pasted = 1235;   // Case 12\n" +
				"		\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"\t\t \tassign pasted = 1234;   // Case 12\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case 12\n"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case13:   IPSOL                                     PCLWS  !PCendCR
		//    Insertion point at start of line, paste code leads with whitespace and ends with code/ws
		//    Expect pasted code to be indented, no change to lines before or after
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"	assign pasted = 1234;   // Case13\n" +
				"	assign pasted = 1235;   // Case13		assign a = 5;\n" +
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"\t   \t\tassign pasted = 1234;   // Case13\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case13"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case14:          IPLWS                              PCLWS  !PCendCR
		//    Insertion point in leading whitespace, pasted code leads with whitespace and ends with code/ws
		//    Expect pasted code to be indented
		//    Loading white space at insertion point to be removed
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" + 
				"\t"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"	assign pasted = 1234;   // Case14\n" +
				"	assign pasted = 1235;   // Case14	assign a = 5;\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"  \t \tassign pasted = 1234;   // Case14\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case14"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case15:                  IPIC                       PCLWS  !PCendCR
		//    Insertion point in code, pasted code leads with whitespace and ends with code/ws
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5\t  \t   /*				assign pasted = 1234;   // Case15*/;\n" +
				"		assign pasted = 1235;\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"\t  \t   /*\t\t\t\tassign pasted = 1234;   // Case15*/;\n" +
				"\t\t\t\t   assign pasted = 1235"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);

		//  Case16:                        IPEOL                PCLWS  !PCendCR
		//    Insertion point in at end of line, pasted code leads with whitespace and ends with code/ws
		//    Expect pasted code to be indented
		tester.setContent(input);
		tester.setCaretOffset(
				(
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;"
				)
				.length());
		expected = 
				"module m(\n" +
				"		input d\n" +
				"	);\n" +
				"\n" +
				"		assign a = 5;  		  assign pasted = 1234;   // Case16\n" +
				"		assign pasted = 1235;   // Case16\n" +		// 1 of the tabs replaced with leading ws
				"			assign a = 6;\n" +
				"				assign a = 7;\n" +
		"				assign a = 8;\n" +
				"endmodule\n";

		tester.paste(
				"  \t\t  assign pasted = 1234;   // Case16\n" +
				"\t\t\t\t   assign pasted = 1235;   // Case16"
				);
		result = tester.getContent();
		fLog.debug("Result:\n'" + result + "'\n");
		IndentComparator.compare("testPasteMultiLine", expected, result);


	}

	public void testPasteModule() throws BadLocationException {
		String first =
			"module t();\n" +
			"logic a;\n" +
			"endmodule\n";

		String text =
			"\n" +
			"	logic a;\n"
			;
		String expected = 
			"module t();\n" +
			"	logic a;\n" +
			"endmodule\n";
		String expected_text = 
				expected + 
				expected + 
				"\n" +
			"logic a;\n" 
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(first);
		tester.paste(first);		// Paste to make sure we get an identical result to when we type stuff
		tester.paste(text);
		
		String content = tester.getContent();
		
		SVCorePlugin.getDefault().enableDebug(false);

		fLog.debug("content=\"" + content + "\"");
		IndentComparator.compare("testPasteModule", expected_text, content);
	}
	
	public void testPasteAlwaysComb() throws BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content =
			"module t;\n" +
			"logic a;\n" +
			"\n" +
			"always_comb begin\n" +
			"a = 0;\n" +
			"end\n" +
			"endmodule\n"
			;
		String paste = 
			"always_comb begin\n" +
			"		a = 0;\n" +
			"	end"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		String result;
		result = tester.getContent();
		
		// Check the initial result
		IndentComparator.compare("testPasteAlwaysComb",
				"module t;\n" +
				"	logic a;\n" +
				"\n" +
				"	always_comb begin\n" +
				"		a = 0;\n" +
				"	end\n" +
				"endmodule\n", result);
		
		tester.setCaretOffset(
				("module t;\n" +
				"	logic a;\n").length()+1);
		
		tester.paste(paste);
		result = tester.getContent();
		
		fLog.debug("result=\"" + result + "\"");
		IndentComparator.compare("testPasteAlwaysComb",
				"module t;\n" +
				"	logic a;\n" +
				"	always_comb begin\n" +
				"		a = 0;\n" +
				"	end\n" +
				"	always_comb begin\n" +
				"		a = 0;\n" +
				"	end\n" +
				"endmodule\n", result);
		SVCorePlugin.getDefault().enableDebug(false);
	}

	public void testModuleWires() throws BadLocationException {
		String content =
			"module t();\n" +
			"logic a;\n" +
			"logic b;\n" +
			"endmodule\n";

		String expected =
			"module t();\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"endmodule\n";
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		tester.paste(content);	// make sure that if we paste the same code, that we get the same if we had typed it
		
		String result = tester.getContent();

		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testModuleWires", expected+expected, result);
	}

	public void testModuleWiresPastePost() throws BadLocationException {
		String content =
			"module t();\n" +
			"logic a;\n" +
			"logic b;\n" +
			"endmodule\n";
		
		String expected =
			"module t();\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"endmodule\n" +
			"module b();\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"endmodule\n";
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		tester.paste(
				"module b();\n" +
				"logic a;\n" +
				"logic b;\n" +
				"endmodule\n");

		
		String result = tester.getContent();

		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testModuleWires", expected, result);
	}

	public void testPasteInModule() throws BadLocationException {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String first =
			"module t();\n" +
			"	logic a;\n" +
			"endmodule\n";

		String text =
			"logic b;\n"
			;
		
		String expected = 
			"module t();\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.setContent(first);
//		tester.type(first);
		tester.setCaretOffset(
				("module t();\n" +
				 "	logic a;\n").length());
		
		tester.paste(text);
		
		String content = tester.getContent();
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare("", expected, content);
	}

	public void testPasteModuleNoCR() throws BadLocationException {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String first =
			"module t;\n" +
			"	logic a;\n" +
			"	always_comb begin\n" +
			"		a = 0;\n" +
			"	end\n" +
			"endmodule"
			;

		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.paste(first);
		
		first += "\n";
		
		String content = tester.getContent();
		
		fLog.debug("Result:\n" + content);
		fLog.debug("Expected:\n" + first);
		IndentComparator.compare("testPasteModuleNoCR", first, content);
	}

	public void testAutoIndentIfThenElse() throws BadLocationException {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content = 
			"module t();\n" +
			"if (foo)\n" +
			"a = 5;\n" +
			"else if (bar)\n" +
			"b = 6;\n" +
			"\n" +
			"if (foo) begin\n" +
			"a = 5;\n" +
			"end else if (bar) begin\n" +
			"b = 6;\n" +
			"end\n" +
			"\n" +
			"if (foo)\n" +
			"begin\n" +
			"a = 5;\n" +
			"end\n" +
			"else\n" +
			"begin\n" +
			"b = 6;\n" +
			"end\n" +
			"endmodule\n"
			;
		String expected = 
			"module t();\n" +
			"	if (foo)\n" +
			"		a = 5;\n" +
			"	else if (bar)\n" +
			"		b = 6;\n" +
			"\n" +
			"	if (foo) begin\n" +
			"		a = 5;\n" +
			"	end else if (bar) begin\n" +
			"		b = 6;\n" +
			"	end\n" +
			"\n" +
			"	if (foo)\n" +
			"	begin\n" +
			"		a = 5;\n" +
			"	end\n" +
			"	else\n" +
			"	begin\n" +
			"		b = 6;\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare("", expected, result);
	}

	
	public void testAutoIndentFor() throws BadLocationException {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content = 
						"module t();\n" +
						"initial\n" +
						"begin\n" +
						"for (i=0; i<10; i++) begin : some_label\n" +
						"for (j=0; j<10; j++)\n" +
						"begin : some_label2\n" +
						"foo = bar;\n" +
						"end\n" +
						"end\n" +
						"end\n" +
						"endmodule\n"
						;
		String expected = 
						"module t();\n" +
						"	initial\n" +
						"	begin\n" +
						"		for (i=0; i<10; i++) begin : some_label\n" +
						"			for (j=0; j<10; j++)\n" +
						"			begin : some_label2\n" +
						"				foo = bar;\n" +
						"			end\n" +
						"		end\n" +
						"	end\n" +
						"endmodule\n"
						;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(content);
		tester.paste(content);	// make sure that paste parses the same as typing
		
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + content);
		IndentComparator.compare("", expected+expected, result);
	}
	
	
	public void testCovergroup() throws BadLocationException {
		String expected =
			"class foobar;\n" +
			"	\n" +
			"	covergroup foobar;\n" +
			"\n" +
			"		var_cp : coverpoint (var) iff (var_cond);\n" +
			"		var1_cp : coverpoint (var) iff (var_cond);\n" +
			"		var2_cp : coverpoint (var) iff (var_cond) {\n" +
			"			bins subrange1[] = {[0:3]};\n" +
			"			bins subrange2[] = {\n" +
			"				[0:3],\n" +
			"				[4:7]\n" +
			"			};\n" +
			"		}\n" +
			"	endgroup\n" +
			"	covergroup cg_1;\n" +
			"		cp_3: coverpoint \n" +
			"		{\n" +
			"			top.bit1,\n" +
			"			top.bit2\n" +
			"		} {\n" +
			"			wildcard bins bin_0 = {2'b?0};\n" +
			"			wildcard bins bin_1 = {2'b?1};\n" +
			"		}\n" +
			"	endgroup\n" +
			"endclass\n";
	
		SVCorePlugin.getDefault().enableDebug(false);
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		
		StringBuilder input = IndentTests.removeLeadingWS(expected);
		tester.type(input.toString());
		String typed_result = tester.getContent();
		
		tester.reset();
		tester.paste(input.toString());
		String pasted_result = tester.getContent();
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		fLog.debug("Typed  Result:\n" + typed_result);
		fLog.debug("Pasted Result:\n" + pasted_result);
		IndentComparator.compare("Covergroup indent failed typing", expected, typed_result);
		IndentComparator.compare("Covergroup indent failed pasting", expected, pasted_result);
	}

	public void testVirtualFunction() throws BadLocationException {
		String input1 = 
			"class foobar;\n\n" +
			"function new();\n" +
			"endfunction\n" +
			"\n" +
			"virtual function string foo();";
		String input2 = "\n" +
			"a = 5;\n" +
			"endfunction\n";
		String expected =
			"class foobar;\n" +
			"	\n" +
			"	function new();\n" +
			"	endfunction\n" +
			"\n" +
			"	virtual function string foo();\n" +
			"		a = 5;\n" +
			"	endfunction\n" +
			"";
		
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input1);
		// SVCorePlugin.getDefault().enableDebug(false);
		tester.type(input2);
		String result = tester.getContent();
		
		
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testVirtualFunction", expected, result);
	}

	public void testTabAtSOL() throws BadLocationException {
		String input1 = 
			"class foobar;\n\n" +
			"function new();\n" +
			"a = 5;\n" +
			"\n" +
			"endfunction\n";
		String input2 =
			"\tb = 6;\n";		// \t at SOL
		String expected =
			"class foobar;\n" +
			"	\n" +
			"	function new();\n" +
			"		a = 5;\n" +
			"		b = 6;\n" +
			"		\n" +
			"	endfunction\n" +
			"";
		
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input1);
		tester.setCaretOffset(42);
//		SVCorePlugin.getDefault().enableDebug(false);
		tester.type(input2);
		String result = tester.getContent();
		
		
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testTabAtSOL", expected, result);
	}

	public void testPastePostStringAdaptiveIndent() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		String content = 
			"class foobar;\n" +
			"\n" +
			"function void foo2();\n" +
			"	$psprintf(\"Hello World\\n    Testing %d\\n\",\n" +
			"		a, b, c);\n\n";
		String expected =
			"class foobar;\n" +
			"\n" +
			"function void foo2();\n" +
			"	$psprintf(\"Hello World\\n    Testing %d\\n\",\n" +
			"		a, b, c);\n" +
			"" +
			"	if (foobar) begin\n" +
			"		a = 6;\n" +
			"	end\n";
		tester.setContent(content);
		//SVCorePlugin.getDefault().enableDebug(false);
		tester.paste(
				"if (foobar) begin\n" +
				"a = 6;\n" +
				"end\n");
		
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testPastePostStringAdaptiveIndent", expected, result);
	}

	public void testPasteAdaptiveIndent() throws BadLocationException {
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		String content = 
			"class foobar;\n" +
			"\n" +
			"function void foo2();\n\n";
		String expected =
			"class foobar;\n" +
			"\n" +
			"function void foo2();\n" +
			"	if (foobar) begin\n" +
			"		a = 6;\n" +
			"	end\n";
		
		tester.setContent(content);
		tester.paste(
				"if (foobar) begin\n" +
				"a = 6;\n" +
				"end\n");
		
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testPasteAdaptiveIndent", expected, result);
	}
	
	public void testPasteInsertOpeningComment() throws BadLocationException {
		String input = 
			"class foo;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		int var;\n" +
			"		var = 5;\n" +
			"		bar = 6;\n" +
			"		*/\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n";
		String expected =
			"class foo;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		int var;\n" +
			"		/*\n" +
			"		var = 5;\n" +
			"		bar = 6;\n" +
			"		*/\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n";
			
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.setContent(input);
		
		tester.setCaretOffset(0);
		while (true) {
			String line = tester.readLine();
			fLog.debug("line=\"" + line + "\"");
			
			if (line.trim().startsWith("int var")) {
				break;
			}
		}
		tester.paste("/*\n");
		
		String result = tester.getContent();
		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testPasteInsertOpeningComment", expected, result);
	}

	public void disabled_testCaseStatement() throws BadLocationException {
		String input = 
			"class foobar;\n" +
			"\n" +
			"function void foobar();\n" +
			"case" +
			"covergroup foobar;\n\n" +
			"var_cp : coverpoint (var) iff (var_cond);\n\n" +
			"var2_cp : coverpoint (var) iff (var_cond) {\n" +
			"bins subrange1[] = {[0:3]};\n" +
			"bins subrange2[] = {\n" +
			"[0:3],\n" +
			"[4:7]\n" +
			"};\n" +
			"}\n" +
			"endgroup\n";
		String expected =
			"class foobar;\n" +
			"\t\n" +
			"\tcovergroup foobar;\n" +
			"\t\t\n" +
			"\t\tvar_cp : coverpoint (var) iff (var_cond);\n" +
			"\t\t\n" +
			"\t\tvar2_cp : coverpoint (var) iff (var_cond) {\n" +
			"\t\t\tbins subrange1[] = {[0:3]};\n" +
			"\t\t\tbins subrange2[] = {\n" +
			"\t\t\t\t[0:3],\n" +
			"\t\t\t\t[4:7]\n" +
			"\t\t\t};\n" +
			"\t\t}\n" +
			"\tendgroup\n" +
			"\t";
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();

		IndentComparator.compare("testCaseStatement", expected, result);
	}
	
	public void testBasedEmptyEnumIndent() throws BadLocationException {
		String input =
			"package p;\n" +
			"typedef enum logic[1:0] {\n" +
			"}\n"
			;
		String expected =
			"package p;\n" +
			"	typedef enum logic[1:0] {\n" +
			"	}\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();

		IndentComparator.compare("testBasedEmptyEnumIndent", expected, result);
	}

	public void testEnumForwardDeclIndent() throws BadLocationException {
		String input =
			"package p;\n" +
			"typedef enum logic[1:0] a;\n" +
			"logic a;\n"
			;
		String expected =
			"package p;\n" +
			"	typedef enum logic[1:0] a;\n" +
			"	logic a;\n";
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();

		IndentComparator.compare("testEnumForwardDeclIndent", expected, result);
	}

	public void testBasedEnumIndent() throws BadLocationException {
		String input =
			"package p;\n" +
			"typedef enum logic[1:0] {\n" +
			"A,\n" +
			"B,\n" +
			"}\n"
			;
		String expected =
			"package p;\n" +
			"	typedef enum logic[1:0] {\n" +
			"		A,\n" +
			"		B,\n" +
			"	}\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();

		IndentComparator.compare("testBasedEnumIndent", expected, result);
	}

	public void testBasedEnumIndentWin() throws BadLocationException {
        String input =
            "package p;\n" +
            "typedef enum logic[1:0] {\n" +
            "A,\n" +
            "B\n" +
            "};\n"
            ;
        String expected =
            "package p;\n" +
            "	typedef enum logic[1:0] {\n" +
            "		A,\n" +
            "		B\n" +
            "	};\n"
            ;
        
        AutoEditTester tester = UiReleaseTests.createAutoEditTester();
        tester.type(input);
        String result = tester.getContent();

        IndentComparator.compare(getName(), expected, result);
        
    }
	
	public void testBasicEnumDecl() throws BadLocationException {
		String input =
			"module t;\n" +
			"typedef enum {\n" +
			"e1, e2\n" +
			"} a;\n"
			;
		String expected =
			"module t;\n" +
			"	typedef enum {\n" +
			"		e1, e2\n" +
			"	} a;\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();

		IndentComparator.compare("testBasicEnumDecl", expected, result);
	}

	public void testProperIndentEndPackage() throws BadLocationException {
		String input =
			"package p;\r\n" +
			"typedef enum logic[1:0] {\r\n" +
			"e0, e1, e2, e3\r" +
    		"} e;\r\n" +
    		"endpackage\r\n" +
    		"\r\n" +
    		"module t1;\r\n" +
    		"endmodule\r\n" +
    		"\r\n";
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();
		
		fLog.debug("Result:\n" + result);
	}

	public void disabled_testModifyIndent() throws BadLocationException {
		int offset1, offset2;
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		
		tester.type("\n\n");
		tester.type("class foobar;\n");
		tester.type("\n");
		offset1 = tester.getCaretOffset();
		tester.type("function void foobar();\n");
		offset2 = tester.getCaretOffset();
		tester.setCaretOffset(offset1);
		tester.type("\n\n");
		tester.setCaretOffset(offset2+3);
		fLog.debug("char @ " + (offset2+2) + " = \"" + tester.getChar() + "\"");
		tester.type("a = 5;\n");
		tester.type("endfunction\n\n");
		tester.type("endclass\n");
		
		String content = tester.getContent();
		
		String expected = 
			"\n\n" +
			"class foobar;\n" +
			"\t\n" +
			"\tfunction void foobar();\n" +
			"\t\ta = 5;\n" +
			"\tendfunction\n" +
			"\t\n" +
			"endclass\n";

		fLog.debug("content=\n" + content);

		assertEquals("Check for expected indent", expected, content);
		
	}

	public void testMoveLineDown() throws BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		String input =
			"module t;\n" +
			"typedef enum {\n" +
			"e1, e2\n" +
			"} a;\n"
			;
		String expected =
			"module t;\n" +
			"\n" +
			"	typedef enum {\n" +
			"		e1, e2\n" +
			"	} a;\n"
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(input);
		String content = tester.getContent();
		int idx = content.indexOf("typedef enum");
		while (content.indexOf(idx) != '\n') {
			idx--;
		}

		tester.setCaretOffset(idx+1);
		fLog.debug("--> type CR");
		tester.type('\n');
		fLog.debug("<-- type CR");
		String result = tester.getContent();

		fLog.debug("Result:\n" + result);
		IndentComparator.compare("testMoveLineDown", expected, result);
	}

	

// This test checks that port lists indent the same as function inputs (if on multiple lines)
public void testModulePorts() throws BadLocationException {
	String input =
		"module p #(\n" +
		"parameter a = 10\n" +
		")\n" +
		"(\n" +
		"input logic a\n" +
		");\n" +
		"typedef enum logic[1:0] {\n" +
		"A,\n" +
		"B\n" +
		"};\n" +
		"function fctn (\n" +
		"input logic a\n" +
		");\n" +
		"endfunction\n" +
		"endmodule"
		;
	String expected =
		"module p #(\n" +
		"		parameter a = 10\n" +
		"		)\n" +
		"		(\n" +
		"		input logic a\n" +
		"		);\n" +
		"	typedef enum logic[1:0] {\n" +
		"		A,\n" +
		"		B\n" +
		"	};\n" +
		"	function fctn (\n" +
		"		input logic a\n" +
		"		);\n" +
		"	endfunction\n" +
		"endmodule"
		;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result = tester.getContent();
	SVCorePlugin.getDefault().enableDebug(false);

	IndentComparator.compare("testModulePorts", expected, result);
}

// This test checks case, casex and casez statments
public void testIndentCase() throws BadLocationException {
	String input =
			"module foo;\n" +
			"always_comb begin\n" +
			"// Case\n" +
			"case (someting)\n" +
			"8'b0000_0000 : begin out = 4'b0000; end\n" +
			"default      : begin\n" +
			"out = '0;\n" +
			"end\n" +
			"endcase\n" +
			"// Case with vector\n" +
			"case (someting[3:2])\n" +
			"8'b0000_0000 : begin out = 4'b0000; end\n" +
			"default      : begin\n" +
			"out = '0;\n" +
			"end\n" +
			"endcase\n" +
			"// casex\n" +
			"casex (someting)\n" +
			"8'b0000_0000 :\n" +
			"begin\n" +
			"out = 4'b0000;\n" +
			"end\n" +
			"default      : out = '0;\n" +
			"endcase\n" +
			"// casez\n" +
			"casez (someting)\n" +
			"8'b0000_0000 : out = 4'b0000;\n" +
			"default      : out = '0;\n" +
			"endcase\n" +
			"end\n" +
			"endmodule\n"
			;
	
	String expected =
			"module foo;\n" +
			"	always_comb begin\n" +
			"		// Case\n" +
			"		case (someting)\n" +
			"			8'b0000_0000 : begin out = 4'b0000; end\n" +
			"			default      : begin\n" +
			"				out = '0;\n" +
			"			end\n" +
			"		endcase\n" +
			"		// Case with vector\n" +
			"		case (someting[3:2])\n" +
			"			8'b0000_0000 : begin out = 4'b0000; end\n" +
			"			default      : begin\n" +
			"				out = '0;\n" +
			"			end\n" +
			"		endcase\n" +
			"		// casex\n" +
			"		casex (someting)\n" +
			"			8'b0000_0000 :\n" +
			"			begin\n" +
			"				out = 4'b0000;\n" +
			"			end\n" +
			"			default      : out = '0;\n" +
			"		endcase\n" +
			"		// casez\n" +
			"		casez (someting)\n" +
			"			8'b0000_0000 : out = 4'b0000;\n" +
			"			default      : out = '0;\n" +
			"		endcase\n" +
			"	end\n" +
			"endmodule\n"
			;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result = tester.getContent();
	
	IndentComparator.compare("testIndentCase", expected, result);
}
// This test checks constraints
public void testIndentConstraint() throws BadLocationException {
	String expected =
			"class someclass;\n" +
			"	constraint clock {\n" +
			"		clk_cfg.period dist {\n" +
			"			[1:10  ] :/ 1,\n" +
			"			11       := 1,\n" +
			"			12       := 1,\n" +
			"			[13: 15] :/ 1\n" +
			"		};\n" + 
			"		clk_cfg.jitter < (3 * 1000);\n" +
			"	}\n" +
			"	constraint frame_sizes {\n" +
			"		size == NORMAL -> {\n" +
			"			length dist {\n" +
			"				[64  :  127 ] := 10,\n" +
			"				[128 :  511 ] := 10,\n" +
			"				[512 :  1500] := 10\n" +
			"			};\n" +
			"		}\n" +
			"		if (size == RUNT)  {\n" +
			"			length >= 0;\n" +
			"			length <= 63;\n" +
			"		}\n" +
			"		else if (size == OVERSIZE) {\n" +
			"			length >= 1501;\n" +
			"			length <= 5000;\n" +
			"		}\n" +
			"	}\n" +
			"	function void my_func;\n" +
			"		my_class cls1; \n" +
			"		assert(cls1.randomize() with {\n" +
			"				cls1.a == 2;\n" +
			"			})\n" +
			"		else $display (\"ERROR\");\n" +
			"	endfunction\n" +
			"endclass\n"
			;
	
	String input = IndentTests.removeLeadingWS(expected).toString();

	SVCorePlugin.getDefault().enableDebug(false);
	SVDefaultIndenter2 indenter = new SVDefaultIndenter2();
	indenter.init(new SVIndentScanner(new StringTextScanner(input)));
	String full_indent = indenter.indent();

	IndentComparator.compare(fLog, getName() + " - full", expected, full_indent);
	
	SVCorePlugin.getDefault().enableDebug(false);
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result_type = tester.getContent();
	
	SVCorePlugin.getDefault().enableDebug(false);
	IndentComparator.compare(fLog, getName() + " - type", expected, result_type);
	
	SVCorePlugin.getDefault().enableDebug(false);
	tester.reset();
	tester.paste(input);
	String result_paste = tester.getContent();
	
	SVCorePlugin.getDefault().enableDebug(false);
	
	IndentComparator.compare(fLog, getName() + " - paste", expected, result_paste);
}

//This test checks assign statements, these can run onto multiple lines
public void testAssignStatements() throws BadLocationException {
	String input =
			"module foo;\n" +
			"assign bob = 1'b0;\n" +
			"assign bob = jane |\n" +
			"jack & \n" +
			"jill;\n" +
			"assign bob = jane ? jack : jill;\n" +
			"assign bob = jane ?\n" +
			"jack :\n" +
			"jill;\n" +
			"endmodule\n"
			;
	
	String expected =
			"module foo;\n" +
			"	assign bob = 1'b0;\n" +
			"	assign bob = jane |\n" +
			"		jack & \n" +
			"		jill;\n" +
			"	assign bob = jane ? jack : jill;\n" +
			"	assign bob = jane ?\n" +
			"		jack :\n" +
			"		jill;\n" +
			"endmodule\n"
			;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result = tester.getContent();
	
	IndentComparator.compare("testAssignStatements", expected, result);
}

//This test checks preprocessor directives. At this point the test only checks:
// - import 
// - `include statements 
// - `define
public void testProgramPreProcDir() throws BadLocationException {
	String input =
			"`include \"global.sv\"\n" +
			"program somep;\n" +
			"import pkg_1::*;\n" +
			"`include \"macros.sv\"\n" +
			"import pkg_2::*;\n" +
			"`define BOB 1\n" +
			"endprogram\n"
			;
	
	String expected =
			"`include \"global.sv\"\n" +
			"program somep;\n" +
			"	import pkg_1::*;\n" +
			"	`include \"macros.sv\"\n" +
			"	import pkg_2::*;\n" +
			"	`define BOB 1\n" +
			"endprogram\n"
			;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result = tester.getContent();
	
	IndentComparator.compare("testProgramPreProcDir", expected, result);
}

//This test multi-line statements
public void testMultiLineStatements() throws BadLocationException {
	String input =
			"program some_pgm;\n" +
			"always @*\n" +
			"begin\n" +
			"jane = bob +\n" +
			"other;\n" +
			"jane = thing + thong;\n" +
			"asdf = 1 + 2;\n" +
			"if ((a ||b) &&\n" +
			"c)\n" +
			"begin\n" +
			"jane = bob +\n" +
			"other;\n" +
			"end\n" +
			"if (\n" +
			"(a > b ()) ||\n" +
			"(b)\n" +
			")\n" +
			"thing = 1;\n" +
			"else if (\n" +
			"(\n" +
			"c ||\n" +
			"d\n" +
			")\n" +
			")\n" +
			"thing2 = 1;\n" +
			"end\n" +
			"assign jane = bob +\n" +
			"other;\n" +
			"endprogram\n"
			;
	
	String expected =
			"program some_pgm;\n" +
			"	always @*\n" +
			"	begin\n" +
			"		jane = bob +\n" +
			"			other;\n" +
			"		jane = thing + thong;\n" +
			"		asdf = 1 + 2;\n" +
			"		if ((a ||b) &&\n" +
			"				c)\n" +
			"		begin\n" +
			"			jane = bob +\n" +
			"				other;\n" +
			"		end\n" +
			"		if (\n" +
			"				(a > b ()) ||\n" +
			"				(b)\n" +
			"			)\n" +
			"			thing = 1;\n" +
			"		else if (\n" +
			"				(\n" +
			"					c ||\n" +
			"					d\n" +
			"				)\n" +
			"			)\n" +
			"			thing2 = 1;\n" +
			"	end\n" +
			"	assign jane = bob +\n" +
			"		other;\n" +
			"endprogram\n"
			;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.paste(input);
	String result = tester.getContent();
	
	IndentComparator.compare("testMultiLineStatements", expected, result);
}



}
