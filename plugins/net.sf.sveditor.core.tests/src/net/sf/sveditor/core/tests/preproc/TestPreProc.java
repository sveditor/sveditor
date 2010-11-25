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
import java.util.Map;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.InputStreamCopier;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

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
			fTmpDir.delete();
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

		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap();
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

		Map<String, SVDBFileTree> ft_map = ((SVDBLibIndex)index).getFileTreeMap();
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
	

}
