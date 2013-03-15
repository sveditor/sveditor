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


package net.sf.sveditor.ui.tests.editor;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.indent.IndentComparator;
import net.sf.sveditor.ui.tests.UiReleaseTests;
import net.sf.sveditor.ui.tests.editor.utils.AutoEditTester;

import org.eclipse.jface.text.BadLocationException;

public class TestAutoIndent extends TestCase {
	
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
		
		System.out.println("Result:\n" + content);
		IndentComparator.compare("testBasicIndent", expected, content);
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
		
		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + result);
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
			"`define INCLUDED_transport_packet_svh\n" +
			"\n" +
			"class vmm_xactor;\n" +
			"\n" +
			"	`VMM_NOTIFY notify;\n"
			;
			
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(first);
		tester.paste(text);
		
		String content = tester.getContent();
		
		System.out.println("Result:\n" + content);
		IndentComparator.compare("testPaste", expected, content);
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
			"	logic a;\n" 
			;
		
		AutoEditTester tester = UiReleaseTests.createAutoEditTester();
		tester.type(first);
		tester.paste(first);		// Paste to make sure we get an identical result to when we type stuff
		tester.setCaretOffset(first.length()*2+1);
		tester.paste(text);
		
		String content = tester.getContent();

		System.out.println("content=\"" + content + "\"");
		IndentComparator.compare("testPasteModule", expected+expected+expected_text, content);
	}
	
	public void testPasteAlwaysComb() throws BadLocationException {
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
		
		System.out.println("result=\"" + result + "\"");
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

		System.out.println("Result:\n" + result);
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

		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + content);
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
		
		System.out.println("Result:\n" + content);
		System.out.println("Expected:\n" + first);
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
		
		System.out.println("Result:\n" + content);
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
		
		System.out.println("Result:\n" + content);
		IndentComparator.compare("", expected+expected, result);
	}
	
	
	public void testCovergroup() throws BadLocationException {
		String input = 
			"class foobar;\n\n" +
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
		

		System.out.println("Result:\n" + result);
		IndentComparator.compare("Covergroup indent failed", expected, result);
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
		
		
		System.out.println("Result:\n" + result);
		IndentComparator.compare("testVirtualFunction", expected, result);
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
		
		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + result);
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
			"/*\n" +
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
			System.out.println("line=\"" + line + "\"");
			
			if (line.trim().startsWith("int var")) {
				break;
			}
		}
		tester.paste("/*\n");
		
		String result = tester.getContent();
		System.out.println("Result:\n" + result);
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
		
		System.out.println("Result:\n" + result);
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
		System.out.println("char @ " + (offset2+2) + " = \"" + tester.getChar() + "\"");
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

		System.out.println("content=\n" + content);

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
		System.out.println("--> type CR");
		tester.type('\n');
		System.out.println("<-- type CR");
		String result = tester.getContent();

		System.out.println("Result:\n" + result);
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
	
	IndentComparator.compare("testModulePorts", expected, result);
}
// This test checks case, casex and casez statments
public void testIndentConstraint() throws BadLocationException {
	String input =
		"class someclass;\n" +
		"constraint clock {\n" +
		"clk_cfg.period dist {\n" +
		"[1:10  ] :/ 1,\n" +
		"11       := 1,\n" +
		"12       := 1,\n" +
		"[13: 15] :/ 1\n" +
		"};\n" +
		"clk_cfg.jitter < (3 * 1000);\n" +
		"}\n" +
		"endclass\n"
		;
	
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
			"endclass\n"
			;
	
	AutoEditTester tester = UiReleaseTests.createAutoEditTester();
	tester.type(input);
	String result = tester.getContent();
	
	IndentComparator.compare("testIndentConstraint", expected, result);
}


}