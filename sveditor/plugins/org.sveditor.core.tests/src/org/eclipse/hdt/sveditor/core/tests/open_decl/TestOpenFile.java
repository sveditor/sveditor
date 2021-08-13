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


package org.eclipse.hdt.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.FileIndexIterator;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import org.eclipse.hdt.sveditor.core.tests.UVMExampleTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.search.SVDBSearchResult;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

public class TestOpenFile extends UVMExampleTestCaseBase {

	public void testRelPathOpenDecl() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		try {
			BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

			utils.copyBundleDirToFS("/data/pkg_rel_path_include/", fTmpDir);
			
			File pkg_rel_path_include = new File(fTmpDir, "pkg_rel_path_include");
			
			String subdir2 = "${workspace_loc}/pkg_rel_path_include/subdir1/subdir2";
			
			IProject project = TestUtils.createProject(
					"pkg_rel_path_include", pkg_rel_path_include);
			addProject(project);
			
			ISVDBIndex target_index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
					"pkg_rel_path_include", subdir2 + "/filelist.f",
					SVDBArgFileIndexFactory.TYPE, null);
			
			target_index.loadIndex(new NullProgressMonitor());

			ISVDBFileSystemProvider fs_provider = 
				((SVDBArgFileIndex)target_index).getFileSystemProvider();

			SVDBFile file = target_index.findFile(subdir2 + "/pkg_rel_path_include.sv");
			
			assertNotNull(file);
			
			InputStream in = fs_provider.openStream(subdir2 + "/pkg_rel_path_include.sv");
			String content = SVCoreTestsPlugin.readStream(in);
			StringBIDITextScanner scanner = new StringBIDITextScanner(content);
			scanner.seek(content.indexOf("target_inc_file.svh")+1);
			fs_provider.closeStream(in);
			
			List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
					file, 4, scanner, target_index);
			
			assertEquals(1, ret.size());
			
			fLog.debug("ret.size=" + ret.size());
			
			fLog.debug("File Path: " + SVDBItem.getName(ret.get(0).first()));
		} finally {
		}
	}

	public void testBasicRelPathOpenDecl() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/basic_rel_path_include/", fTmpDir);

		File basic_rel_path_include = new File(fTmpDir, "basic_rel_path_include");

		//			String subdir2 = "${workspace_loc}/pkg_rel_path_include/subdir1/subdir2";

		IProject project = TestUtils.createProject(
				"basic_rel_path_include", basic_rel_path_include);
		addProject(project);

		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		SVDBIndexCollection index = pdata.getProjectIndexMgr();

		index.rebuildIndex(new NullProgressMonitor());

		ISVDBFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		//				((SVDBArgFileIndex2)target_index).getFileSystemProvider();

		List<SVDBSearchResult<SVDBFile>> f_result = index.findFile(
				"${workspace_loc}/basic_rel_path_include/my_pkg.sv");
		assertNotNull(f_result);
		assertEquals(1, f_result.size());
		SVDBFile file = f_result.get(0).getItem();
		assertNotNull(file);

		InputStream in = fs_provider.openStream(
				"${workspace_loc}/basic_rel_path_include/my_pkg.sv");
		String content = SVCoreTestsPlugin.readStream(in);
		StringBIDITextScanner scanner = new StringBIDITextScanner(content);
		scanner.seek(content.indexOf("src/my_pkg_file1.svh")+1);
		fs_provider.closeStream(in);

		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, 4, scanner, index);

		assertEquals(1, ret.size());

		fLog.debug("ret.size=" + ret.size());

		fLog.debug("File Path: " + SVDBItem.getName(ret.get(0).first()));
	}
	
	public void testOpenFileOutsideWorkspace() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBProjectData pd = setupUBusProject();
	}
	
	public void fixme_testOpenMacroDef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define MY_MACRO foo\n" +		// 1
			"\n" +
			"class c;\n" +
			"	int			`MY_MACRO;\n" +	// 4
			"endclass\n"					// 5
			;
		Tuple<SVDBFile, SVDBFile> file = SVDBTestUtils.parsePreProc(doc, getName(), false);
		SVDBTestUtils.assertFileHasElements(file.second(), "c", "foo");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("`MY_MACRO");
		fLog.debug("index: " + idx);
		scanner.seek(idx+"`MY_".length());

		int lineno = 4;
		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file.second(), lineno, scanner, target_index);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.MacroDef, ret.get(0).first().getType());
		assertEquals("MY_MACRO", SVDBItem.getName(ret.get(0).first()));
	}

}
