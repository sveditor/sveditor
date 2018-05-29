package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.index.IndexTests;
import net.sf.sveditor.core.tests.preproc.SVDBMapFileSystemProvider;

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
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(false);
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
	
	public void testRecoverBehavioralStatement() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"\n" +
			"class my_class;\n" +
			"\n" +
			"	function void foobar;\n" +
			"		int a\n" +
			"		int b;\n" +
			"		int c;\n" +
			"		int d;\n" +
			"	endfunction\n" +
			"\n" +
			"	function void foobar2;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(content, 1, "my_class", "foobar", "foobar2");
	}	
	
	public void testMultiFileErrorRecovery() {
		SVCorePlugin.getDefault().enableDebug(false);
		Map<String, String> file_map = new HashMap<String, String>();
		SVDBMapFileSystemProvider fs_provider = new SVDBMapFileSystemProvider(file_map);
	
		file_map.put("dir/sve.f", 
				"my_pkg.sv\n");
		
		file_map.put("dir/my_pkg.sv", 
				"package my_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"	`include \"cls2.svh\"\n" +
				"	`include \"cls3.svh\"\n" +
				"endpackage\n"
				);
		file_map.put("dir/cls1.svh",
				"class cls1;\n" + 
				"	int a, b, c;\n" +
				"endclass\n"
				);

		file_map.put("dir/cls2.svh",
				"class cls2 foo ;\n" + // error
				"	int a, b, c;\n" +
				"endclass\n"
				);
		
		file_map.put("dir/cls3.svh",
				"class cls3;\n" + 
				"	int a, b, c;\n" +
				"endclass\n"
				);

		runTest(fs_provider, "dir/sve.f", 1, "cls1", "cls3");
	}
	
	public void testMoreThan100ErrorRecovery() {
		SVCorePlugin.getDefault().enableDebug(false);
		Map<String, String> file_map = new HashMap<String, String>();
		SVDBMapFileSystemProvider fs_provider = new SVDBMapFileSystemProvider(file_map);
		
		file_map.put("top_dir/files.f", 
				"top_dir/top.sv\n" +
				"top_dir/m2.sv\n"
				);
		
		StringBuilder sb = new StringBuilder();
		sb.append(
				"	module m ();\n" + 
				"		// comment\n");
		for (int i=0; i<150; i++) {
			sb.append(
				"		assign c=d		// 1\n" + 
				"			assign c=d; // \n");
		}
		
		sb.append(
				"		\n" + 
				"		\n" + 
				"		assign b = c; \n" + 
				"		assign b = c; /* comment */ \n" + 
				"		always @*\n" + 
				"		begin\n" + 
				"			b = c\n" + 
				"		end\n" + 
				"		\n" + 
				"		\n" + 
				"	endmodule\n");
		
		file_map.put("top_dir/top.sv", 
				sb.toString());
		
		file_map.put("top_dir/m2.sv", 
				"module m2 ();\n" + 
				"endmodule\n"
				);
		file_map.put("top_dir/parameters.sv",
				"`define SOME_DEFINE 1'b1\n" + 
				"`define TOP top\n" + 
				"`define MUX `TOP.mux\n"
				);
		
		runTest(fs_provider, "top_dir/files.f", 100, 
				"m" /*, "m_v1"*/, "m2");
	}
	
	private void runTest(String content, int n_errors, String ... expected) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		Tuple<SVDBFile, SVDBFile> ret = SVDBTestUtils.parse(
				fLog, new StringInputStream(content), getName(), markers);
		
		assertEquals(n_errors, markers.size());
		
		SVDBTestUtils.assertFileHasElements(ret.second(), expected);
	}
	
	private void runTest(
			SVDBMapFileSystemProvider 	fs, 
			String 						path, 
			int 						n_errors, 
			String ... 					expected) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), 
				"default", path, 
				SVDBArgFileIndexFactory.TYPE, 
				null);
		index.setFileSystemProvider(fs);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
	
		for (String p : fs.getFileMap().keySet()) {
			List<SVDBMarker> mt = index.getMarkers(p);
			markers.addAll(mt);
		}

		List<String> expected_l = new ArrayList<String>();
		for (String exp : expected) {
			expected_l.add(exp);
		}
		
		for (int i=0; i<expected_l.size(); i++) {
			IndexTests.assertContains(index, expected_l.get(i));
		}
		
		assertEquals(n_errors, markers.size());
		
//		SVDBTestUtils.assertFileHasElements(ret.second(), expected);
	}	
}
