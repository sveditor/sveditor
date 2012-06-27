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


package net.sf.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestOpenFile extends TestCase {
	private File			fTmpDir;
	private IProject		fProject;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getDefault().getSVDBIndexRegistry().save_state();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testRelPathOpenDecl() throws IOException {
		String testname = "testRelPathOpenDecl";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		try {
			BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

			utils.copyBundleDirToFS("/data/pkg_rel_path_include/", fTmpDir);
			
			File subdir2 = new File(fTmpDir, "pkg_rel_path_include/subdir1/subdir2");
			
			fProject = TestUtils.createProject("subdir2", subdir2);
			
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.init(TestIndexCacheFactory.instance(null));
			
			ISVDBIndex target_index = rgy.findCreateIndex(new NullProgressMonitor(),
					"subdir2", "${workspace_loc}/subdir2/pkg_rel_path_include.sv",
					SVDBLibPathIndexFactory.TYPE, null);

			ISVDBItemIterator it = target_index.getItemIterator(new NullProgressMonitor());
			ISVDBFileSystemProvider fs_provider = 
				((SVDBLibIndex)target_index).getFileSystemProvider();
			
			SVDBFile file = null;
			while (it.hasNext()) {
				ISVDBItemBase it_t = it.nextItem();
				if (SVDBItem.getName(it_t).endsWith("pkg_rel_path_include.sv")) {
					file = (SVDBFile)it_t;
				}
			}
			
			InputStream in = fs_provider.openStream("${workspace_loc}/subdir2/pkg_rel_path_include.sv");
			String content = SVCoreTestsPlugin.readStream(in);
			StringBIDITextScanner scanner = new StringBIDITextScanner(content);
			scanner.seek(content.indexOf("target_inc_file.svh")+1);
			fs_provider.closeStream(in);
			
			List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
					file, 4, scanner, target_index);
			
			assertEquals(1, ret.size());
			
			log.debug("ret.size=" + ret.size());
			
			log.debug("File Path: " + SVDBItem.getName(ret.get(0).first()));
		} finally {
		}
		LogFactory.removeLogHandle(log);
	}

	public void testOpenMacroDef() {
		String testname = "testOpenMacroDef";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc =
			"`define MY_MACRO foo\n" +		// 1
			"\n" +
			"class c;\n" +
			"	int			`MY_MACRO;\n" +	// 4
			"endclass\n"					// 5
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "c", "foo");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("`MY_MACRO");
		log.debug("index: " + idx);
		scanner.seek(idx+"`MY_".length());

		int lineno = 4;
		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.MacroDef, ret.get(0).first().getType());
		assertEquals("MY_MACRO", SVDBItem.getName(ret.get(0).first()));
	}

}
