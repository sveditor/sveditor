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

import java.io.ByteArrayOutputStream;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class IndentTests extends SVCoreTestCaseBase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndentTests");
		suite.addTest(new TestSuite(IndentTests.class));
		suite.addTest(new TestSuite(NoHangIndentTests.class));
		suite.addTest(new TestSuite(TestIndentScanner.class));
		suite.addTest(new TestSuite(TestAdaptiveIndent.class));
		
		return suite;
	}
	
	public void testClass() {
		SVCorePlugin.getDefault().enableDebug(false);
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
		
		fLog.debug("Reference:\n" + ref);
		
		fLog.debug("===");
		fLog.debug("Result:\n" + result.toString());
		
		IndentComparator.compare("testClass", ref, result.toString());
	}
	
	public void testBasicCoverpoint() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c1;\n" +
			"\n" +
			"covergroup cg1;\n" +
			"cp : coverpoint a {\n" +
			"bins ab[] = {1, 2, 3, 4};\n" +
			"}\n" +
			"endgroup\n" +
			"endclass\n"
			;
		String expected =
			"class c1;\n" +
			"\n" +
			"	covergroup cg1;\n" +
			"		cp : coverpoint a {\n" +
			"			bins ab[] = {1, 2, 3, 4};\n" +
			"		}\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		fLog.debug("Result:");
		fLog.debug(result);
		IndentComparator.compare(getName(), expected, result);
	}	

	public void testBasicClass() {
		LogHandle log = LogFactory.getLogHandle("testBasicClass");
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
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testBasicClass", expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testBasicCoverpoint_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c1;\n" +
			"\n" +
			"covergroup cg1;\n" +
			"cp : coverpoint a;\n" +
			"cp : coverpoint b;\n" +
			"endgroup\n" +
			"endclass\n"
			;
		String expected =
			"class c1;\n" +
			"\n" +
			"	covergroup cg1;\n" +
			"		cp : coverpoint a;\n" +
			"		cp : coverpoint b;\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		fLog.debug("Result:");
		fLog.debug(result);
		IndentComparator.compare(getName(), expected, result);
	}

	public void testBasicCoverpoint_3() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c1;\n" +
			"\n" +
			"covergroup cg1;\n" +
			"cp : coverpoint\n" +
			"a;\n" +
			"cp : coverpoint\n" +
			"b;\n" +
			"endgroup\n" +
			"endclass\n"
			;
		String expected =
			"class c1;\n" +
			"\n" +
			"	covergroup cg1;\n" +
			"		cp : coverpoint\n" +
			"			a;\n" +
			"		cp : coverpoint\n" +
			"			b;\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		fLog.debug("Result:");
		fLog.debug(result);
		IndentComparator.compare(getName(), expected, result);
	}
	
	public void testEmptyCaseStmt() throws Exception {
		LogHandle log = LogFactory.getLogHandle("testEmptyCaseStmt");
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

		SVCorePlugin.getDefault().enableDebug(false);
		log.debug("--> testEmptyCaseStmt()");
		try {
			SVIndentScanner scanner = new SVIndentScanner(
					new StringTextScanner(content));

			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			indenter.init(scanner);
			indenter.setTestMode(true);

			String result = indenter.indent();

			log.debug("Result:");
			log.debug(result);
			IndentComparator.compare("testEmptyCaseStmt", expected, result);
		} catch (Exception e) {
			e.printStackTrace();
			throw e;
		} finally {
			log.debug("<-- testEmptyCaseStmt()");
		}
		LogFactory.removeLogHandle(log);
	}

	public void testInitialBlock() {
		LogHandle log = LogFactory.getLogHandle("testInitialBlock");
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
		log.debug("--> testInitialBlock");
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testInitialBlock", expected, result);
		log.debug("<-- testInitialBlock");
		
		LogFactory.removeLogHandle(log);
	}

	public void testInitialStmt() {
		LogHandle log = LogFactory.getLogHandle("testInitialStmt");
		String content =
			"module t;\n" +
			"logic a;\n" +
			"initial\n" +
			"a = 5;\n" +
			"logic b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	logic a;\n" +
			"	initial\n" +
			"		a = 5;\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		log.debug("--> testInitialStmt");
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testInitialStmt", expected, result);
		log.debug("<-- testInitialStmt");
		
		LogFactory.removeLogHandle(log);
	}

	public void testStructVar() {
		String testname = "testStructVar";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"struct {\n" +
			"int a;\n" +
			"int b;\n" +
			"} s;\n" +
			"logic b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	struct {\n" +
			"		int a;\n" +
			"		int b;\n" +
			"	} s;\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testTypedefStruct() {
		String testname = "testTypedefStruct";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"typedef struct {\n" +
			"int a;\n" +
			"int b;\n" +
			"} foo_t;\n" +
			"foo_t b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	typedef struct {\n" +
			"		int a;\n" +
			"		int b;\n" +
			"	} foo_t;\n" +
			"	foo_t b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testTypedefNonStructUnion() {
		String testname = "testTypedefNonStructUnion";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"typedef int unsigned uint32_t;\n" +
			"typedef short unsigned uint16_t;\n" +
			"uint32_t foo;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	typedef int unsigned uint32_t;\n" +
			"	typedef short unsigned uint16_t;\n" +
			"	uint32_t foo;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testUnionVar() {
		String testname = "testUnionVar";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"union {\n" +
			"int a;\n" +
			"int b;\n" +
			"} s;\n" +
			"// this is a comment\n" +
			"logic b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	union {\n" +
			"		int a;\n" +
			"		int b;\n" +
			"	} s;\n" +
			"	// this is a comment\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testTypedefUnion() {
		String testname = "testTypedefUnion";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"typedef union {\n" +
			"//comment1\n" +
			"int a;\n" +
			"//comment2\n" +
			"int b;\n" +
			"} foo_t;\n" +
			"//comment3\n" +
			"foo_t b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	typedef union {\n" +
			"		//comment1\n" +
			"		int a;\n" +
			"		//comment2\n" +
			"		int b;\n" +
			"	} foo_t;\n" +
			"	//comment3\n" +
			"	foo_t b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testEnumVar() {
		String testname = "testEnumVar";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"enum {\n" +
			"A,\n" +
			"B\n" +
			"} e;\n" +
			"logic b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	enum {\n" +
			"		A,\n" +
			"		B\n" +
			"	} e;\n" +
			"	logic b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testTypedefEnum() {
		String testname = "testTypedefEnum";
		LogHandle log = LogFactory.getLogHandle(testname);
		String content =
			"module t;\n" +
			"typedef enum {\n" +
			"A,\n" +
			"B\n" +
			"} foo_t;\n" +
			"foo_t b;\n" +
			"endmodule\n"
			;
		String expected =
			"module t;\n" +
			"	typedef enum {\n" +
			"		A,\n" +
			"		B\n" +
			"	} foo_t;\n" +
			"	foo_t b;\n" +
			"endmodule\n"
			;
		log.debug("--> " + testname);
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare(testname, expected, result);
		log.debug("<-- " + testname);
		
		LogFactory.removeLogHandle(log);
	}

	public void testBasicModuleComment() {
		LogHandle log = LogFactory.getLogHandle("testBasicModuleComment");
		String content =
			"module t; // Comment.\n" +
			"logic a;\n" +
			"logic b;\n" +
			"\n" +
			"//comment1\n" +
			"assign a = b;\n" +
			"\n" +
			"//comment2\n" +
			"assign a = \n" +
			"//comment2.1\n" +
			"b;\n" +
			"//comment3\n" +
			"submod sm1 (.a(a),\n" +
			"//comment4\n" +
			".b(b)\n" +
			");\n" +
			"//comment5\n" +
			"endmodule\n" 
			;
		String expected =
			"module t; // Comment.\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"\n" +
			"	//comment1\n" +
			"	assign a = b;\n" +
			"\n" +
			"	//comment2\n" +
			"	assign a = \n" + 
			"		//comment2.1\n" +
			"		b;\n" +
			"	//comment3\n" +
			"	submod sm1 (.a(a),\n" +
			"			//comment4\n" +
			"			.b(b)\n" +
			"			);\n" +
			"	//comment5\n" +
			"endmodule\n" 
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testBasicModuleComment", expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testNestedModule() {
		LogHandle log = LogFactory.getLogHandle("testNestedModule");
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
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testNestedModule", expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testIndentPostSingleComment() {
		LogHandle log = LogFactory.getLogHandle("testIndentPostSingleComment");
		String content =
			"class foo;\n" +					// 1
			"//comment1\n" +
			"function void my_func();\n" +		// 2
			"if (foobar) begin\n" +				// 3
			"end else begin\n" +				// 4
			"// comment block\n" +				// 5
			"a.b = 5;\n" +						// 6
			"end\n" +							// 7
			"endfunction\n" +					// 8
			"//comment2\n" +
			"endclass\n" 						// 9
			;
		String expected =
			"class foo;\n" +
			"	//comment1\n" +
			"	function void my_func();\n" +
			"		if (foobar) begin\n" +
			"		end else begin\n" +
			"			// comment block\n" +
			"			a.b = 5;\n" +
			"		end\n" +
			"	endfunction\n" +
			"	//comment2\n" +
			"endclass\n" 
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testIndentPostSingleComment", expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testBasicModuleWire() {
		LogHandle log = LogFactory.getLogHandle("testBasicModuleWire");
		String content =
			"module top;\n" +
			"// comment1\n" +
			"logic a;\n" +
			"logic b;\n" +
			"// comment2\n" +
			"endmodule\n"
			;
		String expected =
			"module top;\n" +
			"	// comment1\n" +
			"	logic a;\n" +
			"	logic b;\n" +
			"	// comment2\n" +
			"endmodule\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testBasicModuleWire", expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testGenerate() {
		LogHandle log = LogFactory.getLogHandle("testGenerate");
		String content =
			"module t;\n" +
			"parameter a = 0;\n" +
			"generate\n" +
			"if(a == 0) begin\n" +
			"// ...\n" +
			"end\n" +
			"if(a == 1) begin\n" +
			"// ...\n" +
			"end\n" +
			"endgenerate\n" +
			"generate\n" +
			"begin:bob\n" +
			"if(a == 0) begin\n" +
			"// ...\n" +
			"end\n" +
			"if(a == 1) begin\n" +
			"// ...\n" +
			"end\n" +
			"end\n" +
			"endgenerate\n" +
			"endmodule\n"
			;
		String expected =
				"module t;\n" +
				"	parameter a = 0;\n" +
				"	generate\n" +
				"		if(a == 0) begin\n" +
				"			// ...\n" +
				"		end\n" +
				"		if(a == 1) begin\n" +
				"			// ...\n" +
				"		end\n" +
				"	endgenerate\n" +
				"	generate\n" +
				"	begin:bob\n" +
				"		if(a == 0) begin\n" +
				"			// ...\n" +
				"		end\n" +
				"		if(a == 1) begin\n" +
				"			// ...\n" +
				"		end\n" +
				"	end\n" +
				"	endgenerate\n" +
				"endmodule\n"
				;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testGenerate", expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testNewLineIf() {
		LogHandle log = LogFactory.getLogHandle("testNewLineIf");
		String content =
			"\n" +
			"//comment0\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"//comment1\n" +
			"function new();\n" +
			"//comment2\n" +
			"if (foo)\n" +
			"//comment3\n" +
			"foo = 5;\n" +
			"//comment4\n" +
			"else\n" +
			"//comment5\n" +
			"if (foo2) begin\n" +
			"//comment6\n" +
			"foo = 6;\n" +
			"//comment7\n" +
			"end\n" +
			"//comment8\n" +
			"endfunction\n" +
			"//comment9\n" +
			"endclass\n" +
			"//comment10\n"
			;
		String expected =
			"\n" +
			"//comment0\n" +
			"class class1 #(type T=int);\n" +
			"\n" +
			"	//comment1\n" +
			"	function new();\n" +
			"		//comment2\n" +
			"		if (foo)\n" +
			"			//comment3\n" +
			"			foo = 5;\n" +
			"		//comment4\n" +
			"		else\n" +
			"		//comment5\n" +
			"		if (foo2) begin\n" +
			"			//comment6\n" +
			"			foo = 6;\n" +
			"			//comment7\n" +
			"		end\n" +
			"		//comment8\n" +
			"	endfunction\n" +
			"	//comment9\n" +
			"endclass\n" +
			"//comment10\n"
			;
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		log.debug("Result:");
		log.debug(result);
		IndentComparator.compare("testNewLineIf", expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testNoBlockIf() {
		String content =
			"class class1;\n" +
			"\n" +
			"function new();\n" +
			"if (foo)\n" +
			"$display(\"Hello\");\n" +
			"else\n" +
			"$display(\"Goodbye\");\n" +
			"foo = 6;\n" +
			"endfunction\n" +
			"endclass\n"
			;
		String expected =
			"class class1;\n" +
			"\n" +
			"	function new();\n" +
			"		if (foo)\n" +
			"			$display(\"Hello\");\n" +
			"		else\n" +
			"			$display(\"Goodbye\");\n" +
			"		foo = 6;\n" +
			"	endfunction\n" +
			"endclass\n"
			;				
		
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent();
		
		fLog.debug("Result:");
		fLog.debug(result);
		IndentComparator.compare(getName(), expected, result);
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
					log.debug("[OK ]:" + ref_line);
					pass_cnt++;
				} else {
					log.debug("[ERR]:" + ref_line);
					log.debug("[   ]:" + ind_line);
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
		LogHandle log = LogFactory.getLogHandle("testMultiBlankLine");
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
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:");
		log.debug(result);
		log.debug("====");
		
		IndentComparator.compare(log, "testMultiBlankLine", ref, result);
		LogFactory.removeLogHandle(log);
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

			LogHandle log = LogFactory.getLogHandle("testFunctionComment");
			SVCorePlugin.getDefault().enableDebug(false);
			
			// Run the indenter over the reference source
			SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			indenter.init(scanner);
			indenter.setTestMode(true);
			
			String result = indenter.indent(-1, -1);
			
			log.debug("Ref:\n" + ref);
			log.debug("====");
			log.debug("Result:");
			log.debug(result);
			log.debug("====");
			
			IndentComparator.compare(log, "testFunctionComment", ref, result);
			LogFactory.removeLogHandle(log);
	}

	public void testModuleFirstItemComment() {
		String ref = 
		"module foo;\n" +
		"	// this is a comment\n" +
		"	a = 5;\n" +
		"endmodule\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testModuleFirstItemComment");
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, "testModuleFirstItemComment", ref, result);
		LogFactory.removeLogHandle(log);
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
		LogHandle log = LogFactory.getLogHandle("testInitialFirstItemComment");
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);

		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, "testInitialFirstItemComment", ref, result);
		LogFactory.removeLogHandle(log);
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
		LogHandle log = LogFactory.getLogHandle("testFunctionFirstItemComment");
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, "testFunctionFirstItemComment", ref, result);
		LogFactory.removeLogHandle(log);
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
		LogHandle log = LogFactory.getLogHandle("testIfInFunction");
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, "testIfInFunction", ref, result);
		LogFactory.removeLogHandle(log);
	}

	public void testForkJoin() {
		String testname = "testForkJoin";
		String ref =
		"class foo;\n" +
		"	task bar();\n" +
		"		fork\n" +
		"			a();\n" +
		"			b();\n" +
		"		join\n" +
		"	endtask\n" +
		"endclass\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, testname, ref, result);
		LogFactory.removeLogHandle(log);
	}

	public void testEmptyForkJoin() {
		String testname = "testEmptyForkJoin";
		String ref =
		"class foo;\n" +
		"	task bar();\n" +
		"		fork\n" +
		"		join\n" +
		"	endtask\n" +
		"endclass\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, testname, ref, result);
		LogFactory.removeLogHandle(log);
	}

	public void testForkJoinBlock() {
		String testname = "testForkJoinBlock";
		String ref =
		"class foo;\n" +
		"	task bar();\n" +
		"		fork\n" +
		"			begin\n" +
		"				a();\n" +
		"			end\n" +
		"			begin\n" +
		"				b();\n" +
		"			end\n" +
		"		join\n" +
		"	endtask\n" +
		"endclass\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, testname, ref, result);
		LogFactory.removeLogHandle(log);
	}

	public void testPreProcIndent() {
		String testname = "testPreProcIndent";
		String ref =
		"package foo;\n" +
		"	import pkg_1::*;\n" +
		"	`include \"file1.svh\"\n" +
		"	`include \"file2.svh\"\n" +
		"	`include \"file3.svh\"\n" +
		"endpackage\n"
		;
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(ref));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		indenter.setTestMode(true);
		
		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(5);
		String result = indenter.indent(-1, -1);
		
		log.debug("Ref:\n" + ref);
		log.debug("====");
		log.debug("Result:\n" + result);
		log.debug("====");
		
		IndentComparator.compare(log, testname, ref, result);
		LogFactory.removeLogHandle(log);
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
