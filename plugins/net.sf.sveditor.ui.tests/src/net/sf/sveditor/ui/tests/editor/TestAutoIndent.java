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
import net.sf.sveditor.ui.editor.SVAutoIndentStrategy;
import net.sf.sveditor.ui.editor.SVDocumentPartitions;
import net.sf.sveditor.ui.tests.editor.utils.AutoEditTester;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;

public class TestAutoIndent extends TestCase {
	
	private AutoEditTester createAutoEditTester() {
		IDocument doc = new Document();
		AutoEditTester tester = new AutoEditTester(doc, SVDocumentPartitions.SV_PARTITIONING);
		
		tester.setAutoEditStrategy(IDocument.DEFAULT_CONTENT_TYPE, new SVAutoIndentStrategy(null, SVDocumentPartitions.SV_PARTITIONING));
		
		return tester;
	}
	
	public void testBasicIndent() throws BadLocationException {
		AutoEditTester tester = createAutoEditTester();
		
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
		
		assertEquals("Check for expected indent", expected, content);
		
		System.out.println("content=\n" + content);
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
		
		AutoEditTester tester = createAutoEditTester();
		tester.type(first);
		tester.paste(text);
		
		String content = tester.getContent();
		
		System.out.println("content=\"" + content + "\"");
		
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
		
		AutoEditTester tester = createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();
		
		
		if (!expected.equals(result)) {
			System.out.println("result=\"" + result + "\"");
			System.out.println("expected=\"" + expected + "\"");
		}
		assertEquals("Covergroup indent failed", expected, result);
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
			"	\n" +
			"	virtual function string foo();\n" +
			"		a = 5;\n" +
			"	endfunction\n" +
			"	";
		
		
		AutoEditTester tester = createAutoEditTester();
		tester.type(input1);
		// SVCorePlugin.getDefault().enableDebug(true);
		tester.type(input2);
		String result = tester.getContent();
		
		
		if (!expected.equals(result)) {
			System.out.println("result=\"" + result + "\"");
			System.out.println("expected=\"" + expected + "\"");
		}
		assertEquals("Virtual Function indent failed", expected, result);
	}

	public void testPastePostStringAdaptiveIndent() throws BadLocationException {
		AutoEditTester tester = createAutoEditTester();
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
		//SVCorePlugin.getDefault().enableDebug(true);
		tester.paste(
				"if (foobar) begin\n" +
				"a = 6;\n" +
				"end\n");
		
		String result = tester.getContent();
		
		System.out.println("Expected:");
		System.out.println(expected.trim());
		System.out.println("Result:");
		System.out.println(result.trim());
		
		assertEquals("Expected indent result",
				expected.trim(), result.trim());
	}

	public void testPasteAdaptiveIndent() throws BadLocationException {
		AutoEditTester tester = createAutoEditTester();
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
		
		System.out.println("Result:");
		System.out.println(result);
		
		assertEquals("Expected indent result",
				expected.trim(), result.trim());
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
		
		AutoEditTester tester = createAutoEditTester();
		tester.type(input);
		String result = tester.getContent();
		
		
		if (!expected.equals(result)) {
			System.out.println("result=\"" + result + "\"");
			System.out.println("expected=\"" + expected + "\"");
		}
		assertEquals("Covergroup indent failed", expected, result);
	}

	public void disabled_testModifyIndent() throws BadLocationException {
		int offset1, offset2;
		AutoEditTester tester = createAutoEditTester();
		
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
	
}
