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


package org.eclipse.hdt.sveditor.core.tests.index;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.CoreReleaseTests;
import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestArgFileIndex extends SVCoreTestCaseBase {
	
	public void testIncludePathPriority() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testIncludePathPriority");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/arg_file_multi_include/", project);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_multi_include/arg_file_multi_include.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertFileHasElements(index, "class1_dir1");
		IndexTestUtils.assertDoesNotContain(index, "class1_dir2");
		
		LogFactory.removeLogHandle(log);
	}

	public void testAbsIncludePathPriority() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(getName());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/arg_file_multi_include_multi_root/", project);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_multi_include_multi_root/arg_file_multi_include_multi_root.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertDoesNotContain(index, "class1_dir2");
		IndexTestUtils.assertFileHasElements(fLog, index, "class3");

		LogFactory.removeLogHandle(log);
	}

	public void testRelativeIncludeDirective() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(getName());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/arg_file_relative_include_directive/", project);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_relative_include_directive/root/root.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "cls1", "cls2");

		LogFactory.removeLogHandle(log);
	}

	public void testRelativeIncludeDirective2() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(getName());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/arg_file_relative_include_directive2/", project);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_relative_include_directive2/root.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "cls1", "cls2");

		LogFactory.removeLogHandle(log);
	}

	public void testRelativeIncludeDirective3() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(getName());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/arg_file_relative_include_directive3/", project);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_relative_include_directive3/root.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "cls1", "cls2");

		LogFactory.removeLogHandle(log);
	}
	
	public void testWSLibPath() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSLibPath");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/arg_file_libpath/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/arg_file_libpath/arg_file_libpath.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		String names[] = {"a","b","arg_file_libpath_1","arg_file_libpath_2"};
		
		IndexTestUtils.assertFileHasElements(fLog, index, names);

		LogFactory.removeLogHandle(log);
	}

	public void testWindowsPathArgFileInclude() {
		String testname = "testWindowsPathArgFileInclude";
		
		LogHandle log = LogFactory.getLogHandle(testname);
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		IFile file1_f = project_dir.getFile("file1.f");
		TestUtils.copy(
				"-f ${workspace_loc}\\" + testname + "\\file2.f\n" +
				"module_1.sv\n", file1_f);

		IFile file2_f = project_dir.getFile("file2.f");
		TestUtils.copy(
				"module_2.sv\n", file2_f);
		
		IFile module_1_sv = project_dir.getFile("module_1.sv");
		TestUtils.copy(
				"module module_1;\n" +
				"endmodule\n", 
				module_1_sv);
		
		IFile module_2_sv = project_dir.getFile("module_2.sv");
		TestUtils.copy(
				"module module_2;\n" +
				"endmodule\n", 
				module_2_sv);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/file1.f",
				SVDBArgFileIndexFactory.TYPE, null);

		index.loadIndex(new NullProgressMonitor());
	
		IndexTests.assertContains(index, "module_1", SVDBItemType.ModuleDecl);
		IndexTests.assertContains(index, "module_2", SVDBItemType.ModuleDecl);
		
		LogFactory.removeLogHandle(log);
	}
	
	public void testArgFileProjectRelPath() throws CoreException {
		String testname = getName();
		
		LogHandle log = LogFactory.getLogHandle(testname);
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		
		IFile file1_f = project_dir.getFile("file1.f");
		TestUtils.copy(
				"+incdir+subdir\n" +
				"test_pkg.sv\n",
				file1_f);

		IFolder subdir = project_dir.getFolder("subdir");
		subdir.create(true, true, new NullProgressMonitor());
		
		IFile test_pkg_sv = project_dir.getFile("test_pkg.sv");
		TestUtils.copy(
				"package test_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"	`include \"cls2.svh\"\n" +
				"endpackage\n",
				test_pkg_sv);
		
		IFile cls1_svh = project_dir.getFile("cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		IFile cls2_svh = subdir.getFile("cls2.svh");
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				cls2_svh);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "testArgFileProjectRelPath", 
//				"${workspace_loc}/" + testname + "/file1.f",
				"${project_loc}/file1.f",
				SVDBArgFileIndexFactory.TYPE, null);

		index.loadIndex(new NullProgressMonitor());
	
		IndexTests.assertContains(index, "cls1", SVDBItemType.ClassDecl);
		IndexTests.assertContains(index, "cls2", SVDBItemType.ClassDecl);
		
		Iterable<String> filelist = index.getFileList(new NullProgressMonitor());
	
		// Confirm that all paths start with ${workspace_loc}
		for (String path : filelist) {
			assertTrue(path.startsWith("${workspace_loc}"));
			log.debug("File: \"" + path + "\"");
		}
		
		LogFactory.removeLogHandle(log);
	}
	

	public void testArgFileWorkspaceRelPath() throws CoreException {
		String testname = getName();
		
		LogHandle log = LogFactory.getLogHandle(testname);
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		
		IFile file1_f = project_dir.getFile("file1.f");
		TestUtils.copy(
				"+incdir+subdir\n" +
				"test_pkg.sv\n",
				file1_f);

		IFolder subdir = project_dir.getFolder("subdir");
		subdir.create(true, true, new NullProgressMonitor());
		
		IFile test_pkg_sv = project_dir.getFile("test_pkg.sv");
		TestUtils.copy(
				"package test_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"	`include \"cls2.svh\"\n" +
				"endpackage\n",
				test_pkg_sv);
		
		IFile cls1_svh = project_dir.getFile("cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		IFile cls2_svh = subdir.getFile("cls2.svh");
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				cls2_svh);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/file1.f",
				SVDBArgFileIndexFactory.TYPE, null);

		index.loadIndex(new NullProgressMonitor());
	
		IndexTests.assertContains(index, "cls1", SVDBItemType.ClassDecl);
		IndexTests.assertContains(index, "cls2", SVDBItemType.ClassDecl);
		
		Iterable<String> filelist = index.getFileList(new NullProgressMonitor());
	
		// Confirm that all paths start with ${workspace_loc}
		for (String path : filelist) {
			assertTrue(path.startsWith("${workspace_loc}"));
			log.debug("File: \"" + path + "\"");
		}
		
		LogFactory.removeLogHandle(log);
	}
	
	public void testArgFileIncludePath() throws IOException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testArgFileIncludePath");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir_f = new File(fTmpDir, "testArgFileIncludePath_project");
		
		final IProject project_dir = TestUtils.createProject("testArgFileIncludePath_project", project_dir_f);
		addProject(project_dir);

		utils.copyBundleDirToWS("/data/arg_file_include_path/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/testArgFileIncludePath_project/arg_file_include_path/arg_file_include_path.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		SVCorePlugin.setenv("TEST_ENVVAR", fTmpDir.getAbsolutePath() + "/testArgFileIncludePath_project");
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
	
		IndexTestUtils.assertFileHasElements(index, "class1_dir1", "class2", "arg_file_multi_include");

		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testEnvVarExpansion() throws IOException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle("testEnvVarExpansion");
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("testEnvVarExpansion_project");
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/arg_file_env_var/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
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
		
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertFileHasElements(index, "class1", "class2", "ext_pkg_1", "ext_pkg_2");

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
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/multi_arg_file/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "_project/multi_arg_file/multi_arg_file.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
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
		addProject(project_dir);

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
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "_project/multi_arg_file_env_var/multi_arg_file.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertFileHasElements(index, 
				"top_package", "sub_package", "sub_sub_package");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	/**
	 * This test ensures that relative file paths in included argument files are
	 * resolved relative to the directory of the root argument file 
	 * @throws IOException
	 */
	public void testMultiArgFileSingleRootDir() throws IOException {
		String testname = getName();
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		String data_root = "/data/arg_file_multi_include_single_root/";
		utils.copyBundleDirToWS(data_root, project_dir);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/arg_file_multi_include_single_root/arg_file_multi_include.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertDoesNotContain(index, "class1_dir1", "class2_dir2");
		IndexTestUtils.assertFileHasElements(index, "class1_root", "class2_root");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}
	
	public void testMixedSvVlog() throws IOException {
		String testname = getName();
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		String data_root = "/data/arg_file_mixed_sv_vlog/";
		utils.copyBundleDirToWS(data_root, project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/arg_file_mixed_sv_vlog/arg_file_mixed_sv_vlog.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertFileHasElements(index, "my_cls1", "my_cls2", "bit");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}	
	
	public void testMixedSvVlogOverride() throws IOException {
		String testname = getName();
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		String data_root = "/data/index/change_src_levels/";
		utils.copyBundleDirToWS(data_root, project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/change_src_levels/change_src_levels.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "file1_pkg", "file2_pkg");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testMacrosFoundOnTheFlyParse() throws IOException {
		String testname = getName();
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		String data_root = "/data/index/macros_found_onthefly_parse/";
		utils.copyBundleDirToWS(data_root, project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/macros_found_onthefly_parse/macros_found_onthefly_parse.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "root_pkg", "cls1");
		
		String cls1_svh = "${workspace_loc}/" + testname + "/macros_found_onthefly_parse/cls1.svh";
		
		InputStream in = index.getFileSystemProvider().openStream(cls1_svh);
		
		assertNotNull(in);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		fLog.debug("--> Parsing cls1.svh");
		Tuple<SVDBFile, SVDBFile> result = index.parse(new NullProgressMonitor(), in, cls1_svh, markers);
		fLog.debug("<-- Parsing cls1.svh");
		
		for (SVDBMarker m : markers) {
			fLog.debug("Marker: " + m.getMessage());
		}
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}	

	public void testMacrosFoundOnTheFlyParse_2() throws IOException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/macros_found_onthefly_parse_2/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "macros_found_onthefly_parse_2");
	
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/sim/sve.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		/*
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/macros_found_onthefly_parse/macros_found_onthefly_parse.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		 */
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "root_pkg", "cls1");
		
		String cls1_svh = "${workspace_loc}/macros_found_onthefly_parse_2/sv/cls1.svh";

		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		InputStream in = fs_provider.openStream(cls1_svh);
		
		assertNotNull(in);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		fLog.debug("--> Parsing cls1.svh");
		Tuple<SVDBFile, SVDBFile> result = index.parse(new NullProgressMonitor(), in, cls1_svh, markers);
		fLog.debug("<-- Parsing cls1.svh");
		
		for (SVDBMarker m : markers) {
			fLog.debug("Marker: " + m.getMessage());
		}
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}	
	
	public void testMacrosFoundOnTheFlyParse_3() throws IOException, CoreException, URISyntaxException {
		String testname = getName();
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/macros_found_onthefly_parse_3/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "macros_found_onthefly_parse_3");
		
		utils.unpackBundleZipToFS("uvm.zip", fTmpDir);
	
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		IPathVariableManager pvm = project.getPathVariableManager();
		File uvm_home = new File(fTmpDir, "uvm");
		pvm.setURIValue("UVM_HOME", uvm_home.toURI()); // URIUtil.toURI(uvm_home.toURL()));
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/sim/sve.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		/*
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/macros_found_onthefly_parse/macros_found_onthefly_parse.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		 */
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "multi_port_shared_cov_env");
		
		String multi_port_shared_cov_env = "${workspace_loc}/macros_found_onthefly_parse_3/tb/multi_port_shared_cov_env.svh";

		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		InputStream in = fs_provider.openStream(multi_port_shared_cov_env);
		
		assertNotNull(in);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
//		SVCorePlugin.getDefault().enableDebug(false);
		fLog.debug("--> Parsing cls1.svh");
		Tuple<SVDBFile, SVDBFile> result = index.parse(
				new NullProgressMonitor(), 
				in, 
				multi_port_shared_cov_env,
				markers);
		fLog.debug("<-- Parsing cls1.svh");
		
		for (SVDBMarker m : markers) {
			fLog.debug("Marker: " + m.getMessage());
		}
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void testLeafMultimatchInclude() throws IOException, CoreException, URISyntaxException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/leaf_multimatch_include/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "leaf_multimatch_include");
		
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/leaf_multimatch_include.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		/*
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/" + testname + "/macros_found_onthefly_parse/macros_found_onthefly_parse.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		 */
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "my_cls1", "cls1");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testLibDirOption() throws IOException, CoreException, URISyntaxException {
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/libdir/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "libdir");
		
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/libdir.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "top", "m1", "m2");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}	
	
	public void testLibDirOptionMFCU() throws IOException, CoreException, URISyntaxException {
		
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/libdir_mfcu/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "libdir_mfcu");
		
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/libdir_mfcu.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "top", "m1", "m2");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}	
	
	public void testPackageSubInclude() throws IOException, CoreException, URISyntaxException {
		
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		SVCorePlugin.getDefault().enableDebug(false);
		
		String data_root = "/data/index/package_subinclude/";
		utils.copyBundleDirToFS(data_root, fTmpDir);
		
		File project_dir = new File(fTmpDir, "package_subinclude");
		
		final IProject project = TestUtils.createProject(project_dir.getName(), project_dir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/sve.f");
		
		pdata.setProjectFileWrapper(fw);
		

		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(index, "root_pkg", "sub_pkg", "root_cls", "sub_cls");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}	
}
