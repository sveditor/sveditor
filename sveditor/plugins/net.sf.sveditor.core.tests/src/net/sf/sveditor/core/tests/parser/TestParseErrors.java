package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParseErrors extends SVCoreTestCaseBase {
	
	public void testUndefinedMacroGlobalScope() {
		String content = 
			"`UNDEFINED_MACRO(foo, bar)\n" +
			"\n" +
			"class my_class;\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class");
	}
	
	public void testUndefinedMacroClassScope() {
		String content = 
			"\n" +
			"class my_class;\n" +
			"`UNDEFINED_MACRO(foo, bar)\n" +
			"\n" +
			"	function void foobar;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class", "foobar");
	}	

	public void testUndefinedMacroConditionalBeginEndScope() {
		String content = 
			"\n" +
			"class my_class;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		if (a) begin\n" +
			"			`UNDEFINED_MACRO(foo, bar)\n" +
			"		end\n" +
			"	endfunction\n" +
			"\n" +
			"	function void foobar2;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class", "foobar", "foobar2");
	}	

	public void testUndefinedMacroConditionalNoBeginEndScope() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"\n" +
			"class my_class;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		if (a)\n" +
			"			`UNDEFINED_MACRO(foo, bar)\n" +
			"	endfunction\n" +
			"\n" +
			"	function void foobar2;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class", "foobar", "foobar2");
	}	

	public void testUndefinedMacroTFParam() {
		SVCorePlugin.getDefault().enableDebug(true);
		String content = 
			"\n" +
			"class my_class;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		if (a)\n" +
			"			my_tf(`PARAM1, foo, bar);\n" +
			"	endfunction\n" +
			"\n" +
			"	function void foobar2;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class", "foobar", "foobar2");
	}
	
	private void runTest(String content, int n_errors, String ... expected) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		Tuple<SVDBFile, SVDBFile> ret = SVDBTestUtils.parse(
				fLog, new StringInputStream(content), getName(), markers);
		
		assertEquals(n_errors, markers.size());
		
		SVDBTestUtils.assertFileHasElements(ret.second(), expected);
	}
}
