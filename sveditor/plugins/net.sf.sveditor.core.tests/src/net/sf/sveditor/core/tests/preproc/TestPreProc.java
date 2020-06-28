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


package net.sf.sveditor.core.tests.preproc;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestPreProc extends SVCoreTestCaseBase {

	public void testUnbalancedConditionals_GreaterEndifs() {
		String content =
			"\n" +
			"`ifdef FOO\n" +
			"`ifndef BAR\n" +
			"`endif\n" +
			"`endif\n" +
			"`endif\n" +
			"`endif\n" +
			"\n" +
			"\n" +
			"`ifdef FOO\n" + 
			"`endif\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(content);
		
		// A passing test does not cause an exception
	}

	public void testUnbalancedConditionals_InitialElse() {
		String content =
			"\n" +
			"class foo;\n" +
			"`else\n" +
			"endclass\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(content);
		
		// A passing test does not cause an exception
	}

	public void testUnbalancedConditionals_InitialEndif() {
		String content =
			"\n" +
			"class foo;\n" +
			"`endif\n" +
			"endclass\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(content);
		// A passing test does not cause an exception
	}

	public void testElsif_BothFalse() {
		String content =
			"\n" +
			"`ifdef FOO\n" +
			"`elsif BAR\n" +
			"`endif\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(content);
		
		// A passing test does not cause an exception
	}
	
	public void testElsif_ElsifTrue() {
		String content =
			"\n" +
			"`define BAR\n" +
			"`ifdef FOO\n" +
			"`elsif BAR\n" +
			"`endif\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(content);
		
		// A passing test does not cause an exception
	}

	public void testIfdefSplitAcrossFiles() {
		final Map<String, Integer> path2id = new HashMap<String, Integer>();
		final Map<Integer, String> id2path = new HashMap<Integer, String>();
		
		TestUtils.copy(
				"package foo;\n" +
				"`include \"cls1.svh\"\n" +
				"`endif\n" +
				"`include \"cls2.svh\"\n" +
				"endpackage\n",
				new File(fTmpDir, "foo_pkg.sv"));

		TestUtils.copy(
				"class cls1;\n" +
				"`ifdef UNDEFINED\n" +
				"endclass\n",
				new File(fTmpDir, "cls1.svh"));
		
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				new File(fTmpDir, "cls2.svh"));

		InputStream in = TestUtils.openFile(new File(fTmpDir, "foo_pkg.sv"));
		
		SVPreProcessor pp = new SVPreProcessor(getName(), in, 
				new ISVPreProcIncFileProvider() {
					
					@Override
					public Tuple<String, InputStream> findIncFile(String incfile) {
						fLog.debug("findIncFile: " + incfile);
						try {
							File f = new File(fTmpDir, incfile);
							InputStream in = new FileInputStream(f);
								
							fLog.debug("findIncFile: " + f.getAbsolutePath());
							
							return new Tuple<String, InputStream>(f.getAbsolutePath(), in);
						} catch (IOException e) {}
						
						return null;
					}
					
					@Override
					public Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(
							String incfile) {
						fLog.debug("findCachedIncFile: " + incfile);
						// TODO Auto-generated method stub
						return null;
					}
					
					@Override
					public void addCachedIncFile(String incfile, String rootfile) {
						// TODO Auto-generated method stub
						
					}
				}, 
				new ISVPreProcFileMapper() {
					
					@Override
					public int mapFilePathToId(String path, boolean add) {
						if (path2id.containsKey(path)) {
							return path2id.get(path);
						} else if (add) {
							int id = path2id.size()+1;
							path2id.put(path, id);
							id2path.put(id, path);
						}
						return -1;
					}
					
					@Override
					public String mapFileIdToPath(int id) {
						return id2path.get(id);
					}
				});
		SVPreProcOutput out = pp.preprocess();
		
		TestUtils.closeStream(in);
	}
	
	public void testCommaContainingStringMacroParam() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"`define uvm_file `__FILE__\n" +
				"`define uvm_line `__LINE__\n" +
				"`define uvm_fatal(ID,MSG) \\\n" +
				"	begin \\\n" +
				"	if (uvm_report_enabled(UVM_NONE,UVM_FATAL,ID)) \\\n" +
				"		uvm_report_fatal (ID, MSG, UVM_NONE, `uvm_file, `uvm_line); \\\n" +
				"	end\n" +
				"\n" +
				"\n" +
			    "`uvm_fatal(\"PH_BAD_ADD\",\n" +
					"\"cannot add before begin node, after end node, or with end nodes\")\n" +
			    "\n"
				;
			String expected =
				"begin \n" +
				"	if (uvm_report_enabled(UVM_NONE,UVM_FATAL,\"PH_BAD_ADD\")) \n" + 
				"		uvm_report_fatal (\"PH_BAD_ADD\", \"cannot add before begin node, after end node, or with end nodes\", UVM_NONE, " +
					"\"" + getName() + "\", 11); \n" + 
				"	end\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(getName());
			String result = SVDBTestUtils.preprocess(doc, getName());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testMacroBasics_1() {
		String testname = "testMacroBasics_1";
		String doc = 
				"`define MACRO_A 5\n" +
				"int i = `MACRO_A;\n"
				;
			String expected =
				"int i =\n" +
				"5\n" +
				";\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			String result = SVDBTestUtils.preprocess(doc, testname);
			SVCorePlugin.getDefault().enableDebug(false);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testMacroBasics_2() {
		String testname = "testMacroBasics_2";
		String doc = 
				"`define MACRO_A(a) a\n" +
				"int i = `MACRO_A(5);\n"
				;
			String expected =
				"int i =\n" +
				"5\n" +
				";\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			String result = SVDBTestUtils.preprocess(doc, testname);
			SVCorePlugin.getDefault().enableDebug(false);
			
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroBasics_3() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testMacroBasics_3";
		String doc = 
				"`define MACRO_A(a,b) a``b\n" +
				"int i = `MACRO_A(2,5);\n"
				;
			String expected =
				"int i =\n" +
				"25\n" +
				";\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			String result = SVDBTestUtils.preprocess(doc, testname);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroBasics_4() {
		String testname = getName();
		String doc = 
				"`define ABC 123\n" +
				"`define DEF 456\n" +
				"`define GHI 789\n" +
				"\n" +
				"`define MACRO `\"`ABC`\"\n" +
				"\n" +
				"`MACRO\n"
				;
			String expected =
				"\"123\"\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			SVCorePlugin.getDefault().enableDebug(false);
			String result = SVDBTestUtils.preprocess(doc, testname);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroBasics_5() {
		String testname = getName();
		String doc = 
				"`define ABC 123\n" +
				"`define DEF 456\n" +
				"`define GHI 789\n" +
				"\n" +
				"`define MACRO `\"`ABC``-```DEF`\"\n" +
				"\n" +
				"`MACRO\n"
				;
			String expected =
				"\"123-456\"\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			SVCorePlugin.getDefault().enableDebug(false);
			String result = SVDBTestUtils.preprocess(doc, testname);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroBasics_6() {
		String testname = "testMacroBasics_6";
		String doc = 
				"`define ABC  12\n" +
				"`define DEF  34\n" +
				"`define GHI  67\n" +
				"\n" +
				"`define MACRO `\"`ABC``-```DEF`\"\n" +
				"\n" +
				"`MACRO\n"
				;
			String expected =
				"\"12-34\"\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			SVCorePlugin.getDefault().enableDebug(false);
			String result = SVDBTestUtils.preprocess(doc, testname);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testMacroBasics_7() {
		String testname = "testMacroBasics_7";
		String doc = 
				"`define ABC 1\n" +
				"`define DEF 4\n" +
				"`define GHI 7\n" +
				"\n" +
				"`define MACRO `\"`ABC``-```DEF`\"\n" +
				"\n" +
				"`MACRO\n"
				;
			String expected =
				"\"1-4\"\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(testname);
			SVCorePlugin.getDefault().enableDebug(false);
			String result = SVDBTestUtils.preprocess(doc, testname);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testMacroArgExpansion() {
		String doc = 
				"`define test(ID) int MY_``ID``_FIELD\n" +
				"`test(A);\n"
				;
			String expected =
				"int MY_A_FIELD\n" +
				";\n"
				;
				
			LogHandle log = LogFactory.getLogHandle("testMacroArgExpansion");
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgExpansion");
			SVCorePlugin.getDefault().enableDebug(false);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroArgMacroExpansion() {
		String doc = 
				"`define MY_A_FIELD foo\n" +
				"`define MY_B_FIELD bar\n" +
				"`define test(ID) int `MY_``ID``_FIELD\n" +
				"`test(A);\n"
				;
			String expected = 
				"int\n" +
				"foo\n" +
				";\n"
				;
				
			SVCorePlugin.getDefault().enableDebug(false);
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgMacroExpansion");
			
			expected = TestPreProc2.trimLines(expected);
			result = TestPreProc2.trimLines(result);
			
			fLog.debug("Result:\n" + result.trim());
			fLog.debug("====");
			fLog.debug("Expected:\n" + expected.trim());
			fLog.debug("====");
			assertEquals(expected, result);
	}

	public void testMacroArgLastExpansion() {
		String doc = 
				"`define A_SIZED_TO_B(a,b) {{($bits(b)-$bits(a)){1'b0}},a}\n" +
				"\n" +
				"`A_SIZED_TO_B(fred, mary);\n"
				;
		
			String expected = 
				" {{($bits(mary)-$bits(fred)){1'b0}},fred}\n" +
				";\n"
				;
	
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle(getName());
			String result = SVDBTestUtils.preprocess(doc, getName());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testOvmVersion() {
		String doc = 
				"`define OVM_NAME OVM\n" +
				"`define OVM_MAJOR_REV 2\n" +
				"`define OVM_MINOR_REV 0\n" +
				"`define OVM_FIX_REV   3\n" +
				"\n" +
				"`define OVM_VERSION_STRING `\"`OVM_NAME``-```OVM_MAJOR_REV``.```OVM_MINOR_REV``.```OVM_FIX_REV`\"\n" +
				"\n" +
				"`OVM_VERSION_STRING\n"
				;
		
		String expected = 
				"\"OVM-2.0.3\""
				;

		String testname = "testOvmVersion";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);

		result = TestPreProc2.trimLines(result);
		expected = TestPreProc2.trimLines(expected);
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testMacroArgDefaultValue() {
		CoreReleaseTests.clearErrors();
		String doc = 
				"`define MSG(a, b = \"SUFFIX\") $display(a, b);\n" +
				"`MSG(\"FOO\") //Both these result in: unexpected token in primary: \"=\" \n" +
				"`MSG(\"FOO\", \"BAR\")\n"
				;
			String expected = 
				"$display(\"FOO\", \"SUFFIX\");  \n" +
				"$display(\"FOO\", \"BAR\");\n"
					;
				
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle("testMacroArgMacroExpansion");
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgMacroExpansion");
			
			assertEquals("Unexpected errors", 0, CoreReleaseTests.getErrors().size());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testMacroArgDefaultValue_2() {
		String testname = "testMacroArgDefaultValue_2";
		CoreReleaseTests.clearErrors();
		String doc = 
				"`define A_PLUS_B(A, B = 2)  A + B\n" +
				"int a1 = `A_PLUS_B(5, (6 - 2));\n" +
				"int a2 = `A_PLUS_B((6 - 2), 5);\n" +
				"int a3 = `A_PLUS_B((6 - 2), (7 - 5));\n" +
				"int a4 = `A_PLUS_B(5);\n"
				;
			String expected = 
				"int a1 =\n" +
				"5 + (6 - 2)\n" +
				";\n" +
				"int a2 =\n" +
				"(6 - 2) + 5\n" +
				";\n" +
				"int a3 =\n" +
				"(6 - 2) + (7 - 5)\n" +
				";\n" +
				"int a4 =\n" +
				"5 + 2\n" +
				";\n"
					;
				
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle(testname);
			String result = SVDBTestUtils.preprocess(doc, testname);
			
			assertEquals("Unexpected errors", 0, CoreReleaseTests.getErrors().size());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testFileLine() {
		CoreReleaseTests.clearErrors();
		String doc = 
				"uvm_report_warning(\"FOO\", stg,,`__FILE__,`__LINE__);\n" +
				"\n"
				;
			String expected = 
				"uvm_report_warning(\"FOO\", stg,,\"testFileLine\",1);\n"
					;
				
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle("testFileLine");
			String result = SVDBTestUtils.preprocess(doc, "testFileLine");
			
			assertEquals("Unexpected errors", 0, CoreReleaseTests.getErrors().size());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}
	
	public void testUndefExcluded() {
		CoreReleaseTests.clearErrors();
		String doc = 
				"`ifdef UNDEFINED\n" +
				"	content_1\n" +
				"`else\n" +
				"	content_2\n" +
				"`endif\n"
				;
			String expected = 
				"content_2\n"
					;
				
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle("testUndefExcluded");
			String result = SVDBTestUtils.preprocess(doc, "testUndefExcluded");
			
			assertEquals("Unexpected errors", 0, CoreReleaseTests.getErrors().size());
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);		
	}

	public void disabled_testPreProcVMM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_pkg/", project_dir);

		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
	
		/* ISVDBIndex index = */ rgy.findCreateIndex(new NullProgressMonitor(),
				"GLOBAL", "org.vmmcentral.vmm", SVDBPluginLibIndexFactory.TYPE, null);

		/* TEMP:
		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap(new NullProgressMonitor());
		ISVDBFileSystemProvider fs_provider = ((SVDBLibIndex)index).getFileSystemProvider();
		
		SVDBFileTree ft = null;
		for (SVDBFileTree ft_t : ft_map.values()) {
			if (ft_t.getFilePath().endsWith("std_lib/vmm.sv")) {
				ft = ft_t;
				break;
			}
		}
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null);
		mp.setFileContext(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		
		SVPreProcScanner scanner = new SVPreProcScanner();
		scanner.setDefineProvider(dp);
		InputStream in = fs_provider.openStream(ft.getFilePath());
		InputStreamCopier copier = new InputStreamCopier(in);
		
		assertNotNull("Failed to open input", in);
		scanner.init(copier.copy(), ft.getFilePath());
		scanner.setExpandMacros(true);
		scanner.setEvalConditionals(true);
//		scanner.scan();
		
		
		StringBuilder sb = new StringBuilder();
		StringBuilder orig = new StringBuilder();
		int c;
		while ((c = scanner.get_ch()) != -1) {
			sb.append((char)c);
		}
		
		in = copier.copy();
		while (true) {
			try {
				if ((c = in.read()) == -1) {
					break;
				}
				orig.append((char)c);
			} catch (IOException e) { break; }
		}

		fLog.debug("path: " + ft.getFilePath());
		// fLog.debug("Orig is: \n" + orig.toString());
		fLog.debug("Result is: \n" + sb.toString());
		 */
	}

	public void disabled_testNestedMacro() {
		File tmpdir = new File(fTmpDir, "preproc_vmm");
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
	
		/*ISVDBIndex index = */rgy.findCreateIndex(new NullProgressMonitor(), "GLOBAL", 
				"org.vmmcentral.vmm", SVDBPluginLibIndexFactory.TYPE, null);

		/*
		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap(new NullProgressMonitor());
		ISVDBFileSystemProvider fs_provider = ((SVDBLibIndex)index).getFileSystemProvider();
		
		SVDBFileTree ft = null;
		for (SVDBFileTree ft_t : ft_map.values()) {
			if (ft_t.getFilePath().endsWith("std_lib/vmm.sv")) {
				ft = ft_t;
				break;
			}
		}
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null);
		mp.setFileContext(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		
		SVPreProcScanner scanner = new SVPreProcScanner();
		scanner.setDefineProvider(dp);
		InputStream in = fs_provider.openStream(ft.getFilePath());
		InputStreamCopier copier = new InputStreamCopier(in);
		
		assertNotNull("Failed to open input", in);
		scanner.init(copier.copy(), ft.getFilePath());
		scanner.setExpandMacros(true);
		scanner.setEvalConditionals(true);
//		scanner.scan();
		
		
		StringBuilder sb = new StringBuilder();
		StringBuilder orig = new StringBuilder();
		int c;
		while ((c = scanner.get_ch()) != -1) {
			sb.append((char)c);
		}
		
		in = copier.copy();
		while (true) {
			try {
				if ((c = in.read()) == -1) {
					break;
				}
				orig.append((char)c);
			} catch (IOException e) { break; }
		}

		fLog.debug("path: " + ft.getFilePath());
		// fLog.debug("Orig is: \n" + orig.toString());
		fLog.debug("Result is: \n" + sb.toString());
		 */
	}
	
	public void testVmmErrorMacro() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
	        "`define vmm_error(log, msg)  \\\n" +
	        "do \\\n" +
	        "	/* synopsys translate_off */ \\\n" +
	        "	if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, `__FILE__, `__LINE__)) begin \\\n" +
	        "		void'(log.text(msg)); \\\n" +
	        "		log.end_msg(); \\\n" +
	        "	end \\\n" +
	        "	/* synopsys translate_on */ \\\n" +
	        "while (0)\n" +
	        "\n" +
	        "				`vmm_error(log, {\"Self comparison failed: \", diff});\n"
	        ;
		String expected =
			"do \n" + 
			"	   \n" + 
			"	if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, \"testVmmErrorMacro\", 11)) begin \n" + 
			"		void'(log.text({\"Self comparison failed: \", diff})); \n" + 
			"		log.end_msg(); \n" + 
			"	end \n" + 
			"	   \n" +
			"while (0)\n" +
			";\n"
			;
		
		LogHandle log = LogFactory.getLogHandle(getName());
		String result = SVDBTestUtils.preprocess(doc, getName());
		
		expected = TestPreProc2.trimLines(expected);
		result = TestPreProc2.trimLines(result);
		
		log.debug("Result:\n" + result.trim());
		log.debug("====");
		log.debug("Expected:\n" + expected.trim());
		log.debug("====");
		assertEquals(expected.trim(), result.trim());
		LogFactory.removeLogHandle(log);
	}

	public void testOvmSequenceUtilsExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testOvmSequenceUtilsExpansion");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/ovm.zip", fTmpDir);
		utils.copyBundleFileToFS("/data/ovm_sequence_utils_macro.svh", fTmpDir);
		
		PrintStream ps = new PrintStream(new File(fTmpDir, "test.f"));
				
		ps.println("+incdir+./ovm/src");
		ps.println("./ovm/src/ovm_pkg.sv");
		ps.println("./ovm_sequence_utils_macro.svh");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);

		ISVDBIndexInt index = (ISVDBIndexInt)rgy.findCreateIndex(
				new NullProgressMonitor(), "GLOBAL", 
				new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		File target = new File(fTmpDir, "ovm_sequence_utils_macro.svh");
		ISVPreProcessor pp = index.createPreProcScanner(target.getAbsolutePath());
		assertNotNull(pp);
		
		StringBuilder sb = new StringBuilder();
		int ch;
	
		SVPreProcOutput pp_out = pp.preprocess();
		
		while ((ch = pp_out.get_ch()) != -1) {
			sb.append((char)ch);
		}
		log.debug(sb.toString());
		
		assertTrue((sb.indexOf("end )") == -1));
		LogFactory.removeLogHandle(log);
	}

	public void testUvmTlm2DoRecordMacroExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testUvmTlm2DoRecordMacroExpansion");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		utils.copyBundleFileToFS("/data/uvm_tlm2_generic_payload_fields.svh", fTmpDir);
		
		PrintStream ps = new PrintStream(new File(fTmpDir, "test.f"));
				
		ps.println("+incdir+./uvm/src");
		ps.println("./uvm/src/uvm_pkg.sv");
		ps.println("./uvm_tlm2_generic_payload_fields.svh");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);

		ISVDBIndexInt index = (ISVDBIndexInt)rgy.findCreateIndex(
				new NullProgressMonitor(), "GLOBAL", 
				new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		File target = new File(fTmpDir, "uvm_tlm2_generic_payload_fields.svh");
		ISVPreProcessor pp = index.createPreProcScanner(target.getAbsolutePath());
		assertNotNull(pp);
		
		StringBuilder sb = new StringBuilder();
		int ch;
	
		SVPreProcOutput pp_out = pp.preprocess();
		
		while ((ch = pp_out.get_ch()) != -1) {
			sb.append((char)ch);
		}
		log.debug(sb.toString());
		
		assertTrue((sb.indexOf("end )") == -1));
		LogFactory.removeLogHandle(log);
	}
	
	public void testSingleLineCommentMacro() {
		String doc = 
				"`define test_comment(ID) \\\n" +
				"	int LINE1;\\\n" +
				"	// int LINE2;\\\n" +
				"	int LINE3;\n" +
				"\n" +
				"`test_comment(A)\n"
				;
			String expected =
				"int LINE1;\n" +
				"	 \n" +
				"	int LINE3;\n"
				;
				
			LogHandle log = LogFactory.getLogHandle(getName());
			String result = SVDBTestUtils.preprocess(doc, getName());
			SVCorePlugin.getDefault().enableDebug(false);
		
			result = TestPreProc2.trimLines(result);
			expected = TestPreProc2.trimLines(expected);
			log.debug("Result:\n" + result);
			log.debug("====");
			log.debug("Expected:\n" + expected);
			log.debug("====");
			assertEquals(expected, result);
			LogFactory.removeLogHandle(log);
	}

	public void testSpaceSeparatedMacroRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testSpaceSeparatedMacroRef";
		String doc = 
				"`define MY_MACRO(P) ABC P\n" +
				"\n" +
				"` MY_MACRO(A)\n" +
				"`MY_MACRO(B)\n" +
				"`   MY_MACRO(C)\n"
				;
			String expected =
				"ABC A\n" +
				"ABC B\n" +
				"ABC C\n"
				;
				
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);
		
		expected = TestPreProc2.trimLines(expected);
		result = TestPreProc2.trimLines(result);
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testIncompleteMacroRef() {
		String testname = "testIncompleteMacroRef";
		String doc = 
				"`define MY_MACRO(P) ABC P\n" +
				"\n" +
				"` \n" + // Ensure this doesn't trigger a crash
				"`MY_MACRO(A)\n"
				;
			String expected =
				"ABC A\n" 
				;
				
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		result = TestPreProc2.trimLines(result);
		expected = TestPreProc2.trimLines(expected);
		
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);
	}

	public void testMangledMacroRef() {
		String testname = "testMangledMacroRef";
		String doc = 
				"`define MY_MACRO(P) ABC P\n" +
				"\n" +
				"`MY_MACRO(A)\n" +
				"` \n" + // Ensure this doesn't trigger a crash
				"\n" +
				"(\n"
				;
			String expected =
				"ABC A\n" +
				"(\n"
				;
				
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		result = TestPreProc2.trimLines(result);
		expected = TestPreProc2.trimLines(expected);
		
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public void testRecursiveMacroRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testRecursiveMacroRef";
		String doc =
				"//Overly simplistic example\n" +
				"`define M1 `M1\n" +
				" task abc();\n" +
				"	`M1\n" +
				" endtask\n"
				;
		String expected = 
				"task abc();\n" +
				"\t\n" +
				" endtask\n";
		
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);
		
		result = TestPreProc2.trimLines(result);
		expected = TestPreProc2.trimLines(expected);
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);		
	}
	
	public void testRecursiveMacroRef2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = getName(); 
		String doc =
				"//Overly simplistic example\n" +
				"`define M1 `M2\n" +
				"`define M2 `M1\n" +
				" task abc();\n" +
				"	`M1\n" +
				" endtask\n"
				;
		String expected = 
				"task abc();\n" +
				"\t\n" +
				" endtask\n";
		
//		TestCase.fail("Recursion currently broken");
		
		LogHandle log = LogFactory.getLogHandle(testname);
		String result = SVDBTestUtils.preprocess(doc, testname);
		
		result = TestPreProc2.trimLines(result);
		expected = TestPreProc2.trimLines(expected);
		log.debug("Result:\n" + result);
		log.debug("====");
		log.debug("Expected:\n" + expected);
		log.debug("====");
		assertEquals(expected, result);
		LogFactory.removeLogHandle(log);		
	}	
	
	public void testUVMFieldArrayIntExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testUVMFieldArrayIntExpansion");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		PrintStream ps;
		
		// Create uvm_fields.svh
		ps = new PrintStream(new File(fTmpDir, "uvm_fields.svh"));
		ps.println("`include \"uvm_macros.svh\"");
		ps.println();
		ps.println("class uvm_tlm_generic_payload extends uvm_sequence_item;");
		ps.println("	`uvm_object_utils_begin(uvm_tlm_generic_payload)");
//		ps.println("      `uvm_field_int(m_address, UVM_ALL_ON);");
//		ps.println("      `uvm_field_enum(uvm_tlm_command_e, m_command, UVM_ALL_ON);");
		ps.println("      `uvm_field_array_int(m_data, UVM_ALL_ON);");
//		ps.println("      `uvm_field_int(m_length, UVM_ALL_ON);");
//		ps.println("      `uvm_field_enum(uvm_tlm_response_status_e, m_response_status, UVM_ALL_ON);");
//		ps.println("      `uvm_field_array_int(m_byte_enable, UVM_ALL_ON);");
//		ps.println("      `uvm_field_int(m_streaming_width, UVM_ALL_ON);");
		ps.println("	`uvm_object_utils_end");
		ps.println("endclass");
		ps.close();


		// Create test.f
		ps = new PrintStream(new File(fTmpDir, "test.f"));
		ps.println("+define+QUESTA");
		ps.println("+incdir+./uvm/src");
		ps.println("./uvm/src/uvm_pkg.sv");
		ps.println("./uvm_fields.svh");
		ps.flush();
		ps.close();
		
		ISVDBIndexInt index = (ISVDBIndexInt)fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), "GLOBAL", 
				new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		
		File target = new File(fTmpDir, "uvm_fields.svh");
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		InputStream in = index.getFileSystemProvider().openStream(
				target.getAbsolutePath());

		index.parse(new NullProgressMonitor(), in, target.getAbsolutePath(), markers);
		
		index.getFileSystemProvider().closeStream(in);
		
		assertEquals("Errors", 0, markers.size());
		
		index.dispose();
		
//		assertTrue((sb.indexOf("end )") == -1));
		LogFactory.removeLogHandle(log);
	}

	/*
	public void testOvmComponentParamUtilsExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		if (fTmpDir.exists()) {
			assertTrue(TestUtils.delete(fTmpDir));
		}
		assertTrue(fTmpDir.mkdirs());
		
		File db = new File(fTmpDir, "db");
		
		utils.unpackBundleZipToFS("/ovm.zip", fTmpDir);
		utils.copyBundleFileToFS("/data/ovm_component_param_utils_macro.svh", fTmpDir);
		
		PrintStream ps = new PrintStream(new File(fTmpDir, "test.f"));
				
		ps.println("+incdir+./ovm/src");
		ps.println("+incdir+./ovm/examples/xbus/sv");
		ps.println("+incdir+./ovm/examples/xbus/examples");
		ps.println("./ovm/src/ovm_pkg.sv");
		ps.println("./ovm/examples/xbus/examples/xbus_tb_top.sv");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);

		SVDBArgFileIndex index = (SVDBArgFileIndex)rgy.findCreateIndex(
				"GLOBAL", new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		SVPreProcScanner scanner = index.createPreProcScanner("./ovm/examples/xbus/sv/xbus_master_monitor.sv");
		
		StringBuilder sb = new StringBuilder();
		StringBuilder sb2 = new StringBuilder();
		int ch;
		int last_ch=-1;
		int lineno=1;
		
		while ((ch = scanner.get_ch()) != -1) {
			if (last_ch == -1 || last_ch == '\n') {
				sb2.append("" + lineno + ": ");
				lineno++;
			}
			sb.append((char)ch);
			sb2.append((char)ch);
			last_ch=ch;
		}
		fLog.debug(sb2.toString());
		
		SVDBFile file = SVDBTestUtils.parse(sb.toString(), "ovm_in_order_comparator.svh");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		
		assertTrue((sb.indexOf("end )") == -1));
	}
	*/

	private SVPreProcOutput runTest(String content) {
//			SVCorePlugin.getDefault().enableDebug(false);

			InputStream in = new StringInputStream(content);
			SVPreProcessor pp = new SVPreProcessor(getName(), in, null, null);
			return pp.preprocess();
	}
}
