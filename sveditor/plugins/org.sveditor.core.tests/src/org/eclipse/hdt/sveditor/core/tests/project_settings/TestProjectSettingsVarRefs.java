/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.tests.project_settings;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.CoreReleaseTests;
import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.ProjectBuildMonitor;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.SVMarkers;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexUtil;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.hdt.sveditor.core.db.search.SVDBSearchResult;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestProjectSettingsVarRefs extends SVCoreTestCaseBase {
	
	public void disabled_testArgFileWorkspaceRelRef() throws CoreException {
		LogHandle log = LogFactory.getLogHandle(getName());
		SVCorePlugin.getDefault().enableDebug(false);
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS(
				"/data/argfile_projvar_reference/workspace_rel_argfile_ref",
				fTmpDir);
		
		IProject project = TestUtils.importProject(new File(fTmpDir, "workspace_rel_argfile_ref"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		InputStream in = null;

		IFile parameters_sv = root.getFile(new Path("/" + project.getName() + "/top_dir/parameters.sv"));
		in = parameters_sv.getContents();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		List<SVDBSearchResult<SVDBFile>> result = index_collection.findFile(
				"${workspace_loc}/" + project.getName() + "/top_dir/parameters.sv");
		
		IndexTestUtils.assertNoErrWarn(log, index_collection);
		
		// Ensure we can locate the file
		assertEquals(1, result.size());
		
		SVDBFile file = index_collection.parse(new NullProgressMonitor(), in, 
				"${workspace_loc}/" + project.getName() + "/top_dir/parameters.sv", markers).second();
		
		assertNotNull(file);
		assertEquals(0, markers.size());
	}

	public void disabled_testArgFileProjectRelRef() throws CoreException {
		LogHandle log = LogFactory.getLogHandle(getName());
		SVCorePlugin.getDefault().enableDebug(false);
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS(
				"/data/argfile_projvar_reference/project_rel_argfile_ref",
				fTmpDir);
		
		IProject project = TestUtils.importProject(new File(fTmpDir, "project_rel_argfile_ref"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		InputStream in = null;

		IFile parameters_sv = root.getFile(new Path("/" + project.getName() + "/top_dir/parameters.sv"));
		in = parameters_sv.getContents();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		List<SVDBSearchResult<SVDBFile>> result = index_collection.findFile(
				"${workspace_loc}/" + project.getName() + "/top_dir/parameters.sv");
		
		IndexTestUtils.assertNoErrWarn(log, index_collection);
		
		// Ensure we can locate the file
		assertEquals(1, result.size());
		
		SVDBFile file = index_collection.parse(new NullProgressMonitor(), in, 
				"${workspace_loc}/" + project.getName() + "/top_dir/parameters.sv", markers).second();
		
		assertNotNull(file);
		assertEquals(0, markers.size());
	}
	
	public void testResourceVarProjVarRef() throws CoreException {
		// Ignore auto-builds
		SVCorePlugin.setTestModeBuilderDisabled();
		SVCorePlugin.getDefault().enableDebug(false);
		fLog.debug("BEGIN testResourceVarProjVarRef");
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS(
				"/data/argfile_projvar_reference/rvar_rel_argfile_ref",
				fTmpDir);
		
		IProject project = TestUtils.importProject(new File(fTmpDir, "rvar_rel_argfile_ref"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();

		index_collection.rebuildIndex(new NullProgressMonitor());
//		index_collection.loadIndex(new NullProgressMonitor());
	
		InputStream in = null;

		IFile parameters_sv = root.getFile(new Path("/" + project.getName() + "/top_dir/parameters.sv"));
		in = parameters_sv.getContents();
		
		String target_file = "${workspace_loc}/" + project.getName() + "/top_dir/parameters.sv";

		fLog.debug("--> findIndexFile: " + target_file);
		Tuple<ISVDBIndex, SVDBIndexCollection> result = SVDBIndexUtil.findIndexFile(
				target_file, project.getName(), false);
		fLog.debug("<-- findIndexFile: " + target_file);
		
		assertNotNull(result);
		fLog.debug("ISVDBIndex: " + result.first().getBaseLocation());
		fLog.debug("Index Files:");
		for (String file : result.first().getFileList(new NullProgressMonitor())) {
			fLog.debug("  " + file);
		}
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBFile file = IndexTestUtils.parse(result.second(), in, target_file, markers).second();
//		result.second().parse(
//				new NullProgressMonitor(), in, target_file, markers).second();
		
		assertNotNull(file);
		assertEquals(0, markers.size());
		assertEquals(0, CoreReleaseTests.getErrors().size());
		fLog.debug("END testResourceVarProjVarRef");
	}

	public void testProjectDefine() throws CoreException {
		String testname = "testProjectDefine";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS("/data/arg_file_define_proj", fTmpDir);
		
		IProject project = TestUtils.createProject(testname,
				new File(fTmpDir, "arg_file_define_proj"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		
		SVProjectFileWrapper wrapper = pdata.getProjectFileWrapper();
		wrapper.addGlobalDefine("ARG_FILE_DEFINE_PROJ", "1");
		wrapper.addArgFilePath("${workspace_loc}/" + testname + "/arg_file_define_proj.f");
		pdata.setProjectFileWrapper(wrapper);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(index_collection, "arg_file_define_proj");
	}

	public void testProjectDefineChange() throws CoreException {
		String testname = "testProjectDefineChange";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
//		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);

		utils.copyBundleDirToFS("/data/arg_file_define_proj", fTmpDir);
		
//		fProject = TestUtils.importProject(new File(fTmpDir, "arg_file_define_proj"));
		IProject project = TestUtils.createProject(testname,
				new File(fTmpDir, "arg_file_define_proj"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		
		SVProjectFileWrapper wrapper = pdata.getProjectFileWrapper();
		wrapper.addArgFilePath("${workspace_loc}/" + testname + "/arg_file_define_proj.f");
		pdata.setProjectFileWrapper(wrapper);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertDoesNotContain(index_collection, "arg_file_define_proj");
		
		wrapper = pdata.getProjectFileWrapper();
		wrapper.addGlobalDefine("ARG_FILE_DEFINE_PROJ", "1");
		pdata.setProjectFileWrapper(wrapper);
		
		index_collection = pdata.getProjectIndexMgr();
		index_collection.loadIndex(new NullProgressMonitor());
		IndexTestUtils.assertFileHasElements(index_collection, "arg_file_define_proj");
	}
	
	public void testProjectUndefined() throws CoreException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);

		utils.copyBundleDirToFS("/data/arg_file_define_proj", fTmpDir);
		
		IProject project = TestUtils.createProject("arg_file_define_proj",  
				new File(fTmpDir, "arg_file_define_proj"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);

		/*
		SVProjectFileWrapper wrapper = pdata.getProjectFileWrapper();
		wrapper.addGlobalDefine("ARG_FILE_DEFINE_PROJ", "1");
		pdata.setProjectFileWrapper(wrapper);
		 */
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertDoesNotContain(index_collection, "arg_file_define_proj");
	}

	public void testProjectDefine_1() throws CoreException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);

		utils.copyBundleDirToFS("/data/arg_file_define_proj_1", fTmpDir);
		
		IProject project = TestUtils.createProject("arg_file_define_proj_1",  
				new File(fTmpDir, "arg_file_define_proj_1"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);

		SVProjectFileWrapper wrapper = pdata.getProjectFileWrapper();
		wrapper.addArgFilePath("${workspace_loc}/arg_file_define_proj_1/arg_file_define_proj.f");
		wrapper.addGlobalDefine("EXCLUDE_DEFINED", "1");
		pdata.setProjectFileWrapper(wrapper);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(index_collection, "expected_module");
		IndexTestUtils.assertDoesNotContain(index_collection, "arg_file_define_proj");
	}

	/**
	 * Tests that errors are not encountered after an incorrect
	 * argument-file path is changed to the correct one
	 * 
	 * @throws CoreException
	 */
	public void testArgFilePathChange() throws CoreException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);

		utils.copyBundleDirToFS("/data/project_settings_proj1", fTmpDir);
		
		IProject project = TestUtils.importProject(new File(fTmpDir, "project_settings_proj1"));
		addProject(project);
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		SVDBIndexCollection index_collection = null;
		SVProjectFileWrapper fw;
		
		// First, provide an incorrect path to the argument file
		CoreReleaseTests.clearErrors();
		fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/project_settings_proj1/top_dir/files_badpath.f");
		pdata.setProjectFileWrapper(fw, true);
		
		index_collection = pdata.getProjectIndexMgr();
		index_collection.loadIndex(new NullProgressMonitor());
		
		// Ensure that there's at least an error
		assertTrue(CoreReleaseTests.getErrors().size() > 0);
		
		// Now, set the correct path
		CoreReleaseTests.clearErrors();
		fw = pdata.getProjectFileWrapper();
		fw.getArgFilePaths().clear();
		fw.addArgFilePath("${workspace_loc}/project_settings_proj1/top_dir/files.f");
		pdata.setProjectFileWrapper(fw, true);
		
		index_collection = pdata.getProjectIndexMgr();
		index_collection.loadIndex(new NullProgressMonitor());
		
		// Ensure that there are now no errors
		assertTrue(CoreReleaseTests.getErrors().size() == 0);
	}
	
	public void testArgFileInLinkedFolder() throws CoreException, IOException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);

		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		IProject project = TestUtils.createProject("ubus");
		addProject(project);

		File uvm = new File(fTmpDir, "uvm");
		project.getPathVariableManager().setURIValue("UVM_HOME", uvm.toURI());
	
		IFolder ubus = project.getFolder(new Path("ubus"));
		File ubus_d = new File(uvm, "examples/integrated/ubus");
		ubus.createLink(
				ubus_d.toURI(),
				0,
				new NullProgressMonitor());
		
		SVFileUtils.copy(
				"+incdir+${UVM_HOME}/src\n" +
				"${UVM_HOME}/src/uvm_pkg.sv\n" +
				"+incdir+examples\n" +
				"+incdir+sv\n" +
				"examples/ubus_tb_top.sv\n",
				ubus.getFile(new Path("ubus.f")));
				
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		SVDBIndexCollection index_collection = null;
		SVProjectFileWrapper fw;
		
		CoreReleaseTests.clearErrors();
		fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/ubus/ubus/ubus.f");
		pdata.setProjectFileWrapper(fw, true);
		
		index_collection = pdata.getProjectIndexMgr();
		index_collection.loadIndex(new NullProgressMonitor());
		
		String ubus_f = SVFileUtils.readInput(new File(ubus_d, "ubus.f"));
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		index_collection.parse(new NullProgressMonitor(), 
				new StringInputStream(ubus_f), 
				"${workspace_loc}/ubus/ubus/ubus.f",
				markers);
		
		// Ensure that there are now no errors
		assertTrue(CoreReleaseTests.getErrors().size() == 0);		
	}

}
