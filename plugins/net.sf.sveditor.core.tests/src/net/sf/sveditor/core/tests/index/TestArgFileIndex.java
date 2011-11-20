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


package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestArgFileIndex extends TestCase {
	
	private File				fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
//		TestUtils.delete(fTmpDir);
	}

	public void testIncludePathPriority() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testIncludePathPriority");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/arg_file_multi_include/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_multi_include/arg_file_multi_include.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1_dir1 = null, class1_dir2 = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("Item: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1_dir1")) {
				class1_dir1 = tmp_it;
			} else if (name.equals("class1_dir2")) {
				class1_dir2 = tmp_it;
			}
		}
		
		assertNull("Incorrectly found class1_dir2", class1_dir2);
		assertNotNull("Failed to find class1_dir1", class1_dir1);
		LogFactory.removeLogHandle(log);
	}

	public void testWSLibPath() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSLibPath");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/arg_file_libpath/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_libpath/arg_file_libpath.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		String names[] = {"a","b","arg_file_libpath_1","arg_file_libpath_2"};
	
		for (String n : names) {
			List<SVDBDeclCacheItem> res = index.findGlobalScopeDecl(
					new NullProgressMonitor(), n, 
					SVDBFindDefaultNameMatcher.getDefault());
			assertEquals("Find of \"" + n + "\" failed: ", 1, res.size());
		}
		
		LogFactory.removeLogHandle(log);
	}

	public void testArgFileIncludePath() throws IOException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testArgFileIncludePath");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir_f = new File(fTmpDir, "testArgFileIncludePath_project");
		
		if (project_dir_f.exists()) {
			TestUtils.delete(project_dir_f);
		}
		
		final IProject project_dir = TestUtils.createProject("testArgFileIncludePath_project", project_dir_f);
		utils.copyBundleDirToWS("/data/arg_file_include_path/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/testArgFileIncludePath_project/arg_file_include_path/arg_file_include_path.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		SVCorePlugin.setenv("TEST_ENVVAR", fTmpDir.getAbsolutePath() + "/testArgFileIncludePath_project");
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null, class2 = null;
		ISVDBItemBase arg_file_multi_include = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("Item: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1_dir1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("arg_file_multi_include")) {
				arg_file_multi_include = tmp_it;
			} 
		}

		assertNotNull(class1);
		assertNotNull(class2);
		assertNotNull(arg_file_multi_include);
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testEnvVarExpansion() throws IOException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle("testEnvVarExpansion");
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("testEnvVarExpansion_project");
		
		utils.copyBundleDirToWS("/data/arg_file_env_var/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/testEnvVarExpansion_project/arg_file_env_var/arg_file_env_var.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		SVCorePlugin.setenv("EXT_LIB", fTmpDir.getAbsolutePath() + "/ext_lib");
		
		File ext_lib = new File(fTmpDir, "/ext_lib");
		ext_lib.mkdirs();
		
		PrintStream ps;
		ps = new PrintStream(new File(ext_lib, "ext_pkg_1.sv"));
		ps.println("package ext_pkg_1;");
		ps.println("    class ext_cl1;");
		ps.println("    endclass");
		ps.println("endpackage");
		ps.close();

		ps = new PrintStream(new File(ext_lib, "ext_pkg_2.sv"));
		ps.println("package ext_pkg_2;");
		ps.println("    class ext_cl2;");
		ps.println("    endclass");
		ps.println("endpackage");
		ps.close();

		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null, class2 = null;
		ISVDBItemBase ext_pkg_1 = null, ext_pkg_2 = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("Item: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("ext_pkg_1")) {
				ext_pkg_1 = tmp_it;
			} else if (name.equals("ext_pkg_2")) {
				ext_pkg_2 = tmp_it;
			}
		}

		assertNotNull(class1);
		assertNotNull(class2);
		assertNotNull(ext_pkg_1);
		assertNotNull(ext_pkg_2);
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testMultiArgFile() throws IOException {
		String testname = "testMultiArgFile";
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname + "_project");
		
		utils.copyBundleDirToWS("/data/multi_arg_file/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "_project/multi_arg_file/multi_arg_file.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		IndexTestUtils.assertFileHasElements(index, 
				"top_package", "sub_package", "sub_sub_package");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testMultiArgFileEnvVar() throws IOException {
		String testname = "testMultiArgFileEnvVar";
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname + "_project");
		File proj_subdir = new File(fTmpDir, "proj_subdir");
		assertTrue(proj_subdir.mkdirs());
		
		SVCorePlugin.setenv("PROJ_SUBDIR", proj_subdir.getAbsolutePath());
		
		String data_root = "/data/multi_arg_file_env_var/";
		utils.copyBundleDirToWS(data_root, project_dir);
		for (String f : new String[] {"sub_arg_file.f", "sub_package.sv", "sub_sub_arg_file.f",
					"sub_sub_package.sv"}) {
			utils.copyBundleFileToFS(data_root + f, proj_subdir);
			assertTrue(utils.deleteWSFile(project_dir, "multi_arg_file_env_var/"));
		}
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "_project/multi_arg_file_env_var/multi_arg_file.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		IndexTestUtils.assertFileHasElements(index, 
				"top_package", "sub_package", "sub_sub_package");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

}
