package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParseExpr extends TestCase {

	public void testTimeUnits() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		time t_s = 0.5s;\n" +
			"		time t_ms = 0.5ms;\n" +
			"		time t_us = 0.5us;\n" +
			"		time t_ns = 0.5ns;\n" +
			"		time t_ps = 0.5ps;\n" +
			"		time t_fs = 0.5fs;\n" +
			"		time t_1s = 1s;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", "t_s", "t_ms", "t_us",
					"t_ns", "t_ps", "t_fs", "t_1s"});
	}

	public void testStreamOperators() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		int a, b, c;\n" +
			"		logic [10:0] up [3:0];\n" +
			"		logic [11:1] p1, p2, p3, p4;\n" +
			"		bit [96:1] y = {>>{ a, b, c }}; // OK: pack a, b, c\n" +
			"		int j = {>>{ a, b, c }}; // error: j is 32 bits < 96 bits\n" +
			"		bit [99:0] d = {>>{ a, b, c }}; // OK: b is padded with 4 bits\n" +
			"		{>>{ a, b, c }} = 23'b1; // error: too few bits in stream\n" +
			"		{>>{ a, b, c }} = 96'b1; // OK: unpack a = 0, b = 0, c = 1\n" +
			"		{>>{ a, b, c }} = 100'b1; // OK: unpack as above (4 bits unread)\n" +
			"		{ >> {p1, p2, p3, p4}} = up; // OK: unpack p1 = up[3], p2 = up[2],\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", 
					"a", "b", "c", "up", "p1", "y"});
	}

	public void testStringEmbeddedBackslashes() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"\n" +
			"	function do_something;\n" +
			"		if (my_string == \"\\\\\")\n" +
			"			$display(\"Hello World\");\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testStringEmbeddedBackslashes", content,
				new String[] {"my_class", "do_something"});
	}

	public void testStringEmbeddedComment() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class;\n" +
			"\n" +
			"	function do_something;\n" +
			"		if (my_string == \"\\\\\")\n" +
			"			$display(\"Hello World // this is a comment\");\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testStringEmbeddedComment", content,
				new String[] {"my_class", "do_something"});
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}
}
