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
import java.util.Map;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.InputStreamCopier;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestPreProc extends TestCase {

	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		System.out.println("setUp");
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		System.out.println("tearDown");
		super.tearDown();

		if (fTmpDir != null) {
//			fTmpDir.delete();
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
	

	public void disabled_testPreProcVMM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_pkg/", project_dir);

		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
	
		ISVDBIndex index = rgy.findCreateIndex("GLOBAL", "org.vmmcentral.vmm", 
					SVDBPluginLibIndexFactory.TYPE, null);

		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap(new NullProgressMonitor());
		ISVDBFileSystemProvider fs_provider = ((SVDBLibIndex)index).getFileSystemProvider();
		
		SVDBFileTree ft = null;
		for (SVDBFileTree ft_t : ft_map.values()) {
			if (ft_t.getFilePath().endsWith("std_lib/vmm.sv")) {
				ft = ft_t;
				break;
			}
		}
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider();
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
	}

	public void disabled_testNestedMacro() {
		File tmpdir = new File(fTmpDir, "preproc_vmm");
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(tmpdir);
	
		ISVDBIndex index = rgy.findCreateIndex("GLOBAL", "org.vmmcentral.vmm", 
					SVDBPluginLibIndexFactory.TYPE, null);

		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap(new NullProgressMonitor());
		ISVDBFileSystemProvider fs_provider = ((SVDBLibIndex)index).getFileSystemProvider();
		
		SVDBFileTree ft = null;
		for (SVDBFileTree ft_t : ft_map.values()) {
			if (ft_t.getFilePath().endsWith("std_lib/vmm.sv")) {
				ft = ft_t;
				break;
			}
		}
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider();
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
			
		String result = SVDBTestUtils.preprocess(doc, "testVmmErrorMacro");
		
		System.out.println("Result:\n" + result.trim());
		System.out.println("====");
		System.out.println("Expected:\n" + expected.trim());
		System.out.println("====");
		assertEquals(expected.trim(), result.trim());
	}

	public void testOvmSequenceUtilsExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		if (fTmpDir.exists()) {
			assertTrue(fTmpDir.delete());
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
		rgy.init(db);

		SVDBArgFileIndex index = (SVDBArgFileIndex)rgy.findCreateIndex(
				"GLOBAL", new File(fTmpDir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		File target = new File(fTmpDir, "ovm_sequence_utils_macro.svh");
		SVPreProcScanner scanner = index.createPreProcScanner(target.getAbsolutePath());
		
		StringBuilder sb = new StringBuilder();
		int ch;
		
		while ((ch = scanner.get_ch()) != -1) {
			sb.append((char)ch);
		}
		System.out.println(sb.toString());
		
		assertTrue((sb.indexOf("end )") == -1));
	}

	/*
	public void testOvmComponentParamUtilsExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(true);
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		if (fTmpDir.exists()) {
			assertTrue(fTmpDir.delete());
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
