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


package net.sf.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.old.SVDBLibIndex;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestOpenFile extends SVCoreTestCaseBase {

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
				((SVDBArgFileIndex2)target_index).getFileSystemProvider();

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
	
	public void fixme_testOpenMacroDef() {
		SVCorePlugin.getDefault().enableDebug(true);
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
