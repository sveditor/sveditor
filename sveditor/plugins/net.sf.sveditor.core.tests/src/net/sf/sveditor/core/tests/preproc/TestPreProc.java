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


package net.sf.sveditor.core.tests.preproc;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestPreProc extends TestCase {

	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();

		SVCorePlugin.getDefault().getSVDBIndexRegistry().save_state();
		
		if (fTmpDir != null) {
			TestUtils.delete(fTmpDir);
			fTmpDir = null;
		}
	}
	
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

		InputStream in = new StringInputStream(content);
		SVPreProcScanner pp_scanner = new SVPreProcScanner();
		pp_scanner.init(in, "content");
		SVDBPreProcObserver observer = new SVDBPreProcObserver();
		pp_scanner.setObserver(observer);
		pp_scanner.scan();
		
		// A passing test does not cause an exception
	}
	
	public void testCommaContainingStringMacroParam() {
		String doc = 
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
				"		uvm_report_fatal (\"PH_BAD_ADD\", \"cannot add before begin node, after end node, or with end nodes\", UVM_NONE, e, e); \n" + 
				"	end\n"
				;
				
			LogHandle log = LogFactory.getLogHandle("testCommaContainingStringMacroParam");
			String result = SVDBTestUtils.preprocess(doc, "testCommaContainingStringMacroParam");
			SVCorePlugin.getDefault().enableDebug(false);
			
			log.debug("Result:\n" + result.trim());
			log.debug("====");
			log.debug("Expected:\n" + expected.trim());
			log.debug("====");
			assertEquals(expected.trim(), result.trim());
			LogFactory.removeLogHandle(log);
	}
	
	public void testMacroArgExpansion() {
		String doc = 
				"`define test(ID) int MY_``ID``_FIELD\n" +
				"`test(A);\n"
				;
			String expected =
				"int MY_A_FIELD;\n"
				;
				
			LogHandle log = LogFactory.getLogHandle("testMacroArgExpansion");
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgExpansion");
			SVCorePlugin.getDefault().enableDebug(false);
			
			log.debug("Result:\n" + result.trim());
			log.debug("====");
			log.debug("Expected:\n" + expected.trim());
			log.debug("====");
			assertEquals(expected.trim(), result.trim());
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
				"int  foo;\n"
				;
				
			SVCorePlugin.getDefault().enableDebug(false);
			LogHandle log = LogFactory.getLogHandle("testMacroArgMacroExpansion");
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgMacroExpansion");
			
			log.debug("Result:\n" + result.trim());
			log.debug("====");
			log.debug("Expected:\n" + expected.trim());
			log.debug("====");
			assertEquals(expected.trim(), result.trim());
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
				"$display(\"FOO\", \"SUFFIX\");" +
				"    $display(\"FOO\", \"BAR\");\n"
					;
				
			SVCorePlugin.getDefault().enableDebug(true);
			LogHandle log = LogFactory.getLogHandle("testMacroArgMacroExpansion");
			String result = SVDBTestUtils.preprocess(doc, "testMacroArgMacroExpansion");
			
			assertEquals("Unexpected errors", 0, CoreReleaseTests.getErrors().size());
			
			log.debug("Result:\n" + result.trim());
			log.debug("====");
			log.debug("Expected:\n" + expected.trim());
			log.debug("====");
			assertEquals(expected.trim(), result.trim());
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
		rgy.init(TestIndexCacheFactory.instance(project_dir));
	
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

		System.out.println("path: " + ft.getFilePath());
		// System.out.println("Orig is: \n" + orig.toString());
		System.out.println("Result is: \n" + sb.toString());
		 */
	}

	public void disabled_testNestedMacro() {
		File tmpdir = new File(fTmpDir, "preproc_vmm");
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(tmpdir));
	
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

		System.out.println("path: " + ft.getFilePath());
		// System.out.println("Orig is: \n" + orig.toString());
		System.out.println("Result is: \n" + sb.toString());
		 */
	}
	
	public void testVmmErrorMacro() {
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
			"	/* synopsys translate_off */ \n" + 
			"	if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, \"testVmmErrorMacro\", 0)) begin \n" + 
			"		void'(log.text({\"Self comparison failed: \", diff})); \n" + 
			"		log.end_msg(); \n" + 
			"	end \n" + 
			"	/* synopsys translate_on */ \n" + 
			"while (0); \n"
			;
			
		LogHandle log = LogFactory.getLogHandle("testVmmErrorMacro");
		String result = SVDBTestUtils.preprocess(doc, "testVmmErrorMacro");
		
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
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
		assertTrue(fTmpDir.mkdirs());
		
		File db = new File(fTmpDir, "db");
		
		utils.unpackBundleZipToFS("/ovm.zip", fTmpDir);
		utils.copyBundleFileToFS("/data/ovm_sequence_utils_macro.svh", fTmpDir);
		
		PrintStream ps = new PrintStream(new File(fTmpDir, "test.f"));
				
		ps.println("+incdir+./ovm/src");
		ps.println("./ovm/src/ovm_pkg.sv");
		ps.println("./ovm_sequence_utils_macro.svh");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));

		SVDBArgFileIndex index = (SVDBArgFileIndex)rgy.findCreateIndex(
				new NullProgressMonitor(), "GLOBAL", 
				new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		File target = new File(fTmpDir, "ovm_sequence_utils_macro.svh");
		SVPreProcScanner scanner = index.createPreProcScanner(target.getAbsolutePath());
		assertNotNull(scanner);
		
		StringBuilder sb = new StringBuilder();
		int ch;
		
		while ((ch = scanner.get_ch()) != -1) {
			sb.append((char)ch);
		}
		log.debug(sb.toString());
		scanner.close();
		
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
				"	// int LINE2;\n" +
				"	int LINE3;\n"
				;
				
			LogHandle log = LogFactory.getLogHandle("testSingleLineCommentMacro");
			String result = SVDBTestUtils.preprocess(doc, "testSingleLineCommentMacro");
			SVCorePlugin.getDefault().enableDebug(false);
			
			log.debug("Result:\n" + result.trim());
			log.debug("====");
			log.debug("Expected:\n" + expected.trim());
			log.debug("====");
			assertEquals(expected.trim(), result.trim());
			LogFactory.removeLogHandle(log);
	}

	public void testUVMFieldArrayIntExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testUVMFieldArrayIntExpansion");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
		assertTrue(fTmpDir.mkdirs());
		
		File db = new File(fTmpDir, "db");
		
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
		ps.println("+incdir+./uvm/src");
		ps.println("./uvm/src/uvm_pkg.sv");
		ps.println("./uvm_fields.svh");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));

		SVDBArgFileIndex index = (SVDBArgFileIndex)rgy.findCreateIndex(
				new NullProgressMonitor(), "GLOBAL", 
				new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		File target = new File(fTmpDir, "uvm_fields.svh");
		SVPreProcScanner scanner = index.createPreProcScanner(target.getAbsolutePath());
		assertNotNull(scanner);
		
		StringBuilder sb = new StringBuilder();
		int ch;
		
		while ((ch = scanner.get_ch()) != -1) {
			sb.append((char)ch);
		}
		int lineno=1;
		StringBuilder line = new StringBuilder();
		for (int i=0; i<sb.length(); i++) {
			while (i<sb.length() && sb.charAt(i) != '\n') {
				if (sb.charAt(i) != '\r') {
					line.append(sb.charAt(i));
				}
				i++;
			}
			if (sb.charAt(i) == '\n') {
				i++;
			}
			log.debug(lineno + ": " + line.toString());
			line.setLength(0);
			lineno++;
		}
		scanner.close();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = SVDBTestUtils.parse(log, sb.toString(), "uvm_fields.svh", markers);
		
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
		System.out.println(sb2.toString());
		
		SVDBFile file = SVDBTestUtils.parse(sb.toString(), "ovm_in_order_comparator.svh");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		
		assertTrue((sb.indexOf("end )") == -1));
	}
	*/

}
