package net.sf.sveditor.core.tests.project_settings;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class TestProjectSettingsVarRefs extends TestCase {
	private File				fTmpDir;
	private IProject			fProject;
	
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		} 
	}

	public void testArgFileWorkspaceRelRef() throws CoreException {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS(
				"/data/argfile_projvar_reference/workspace_rel_argfile_ref",
				fTmpDir);
		
		fProject = TestUtils.importProject(new File(fTmpDir, "workspace_rel_argfile_ref"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		InputStream in = null;

		IFile parameters_sv = root.getFile(new Path("/" + fProject.getName() + "/top_dir/parameters.sv"));
		in = parameters_sv.getContents();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBFile file = index_collection.parse(new NullProgressMonitor(), in, 
				"${workspace_loc}/" + fProject.getName() + "/top_dir/parameters.sv", markers).second();
		
		assertNotNull(file);
		assertEquals(0, markers.size());
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void testResourceVarProjVarRef() throws CoreException {
		String testname = "testResourceVarProjVarRef";
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS(
				"/data/argfile_projvar_reference/rvar_rel_argfile_ref",
				fTmpDir);
		
		fProject = TestUtils.importProject(new File(fTmpDir, "rvar_rel_argfile_ref"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
	
		InputStream in = null;

		IFile parameters_sv = root.getFile(new Path("/" + fProject.getName() + "/top_dir/parameters.sv"));
		in = parameters_sv.getContents();
		
		String target_file = "${workspace_loc}/" + fProject.getName() + "/top_dir/parameters.sv";
		
		Tuple<ISVDBIndex, SVDBIndexCollection> result = SVDBIndexUtil.findIndexFile(
				target_file, fProject.getName(), false);
		
		assertNotNull(result);
		log.debug("ISVDBIndex: " + result.first().getBaseLocation());
		log.debug("Index Files:");
		for (String file : result.first().getFileList(new NullProgressMonitor())) {
			log.debug("  " + file);
		}
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBFile file = result.second().parse(
				new NullProgressMonitor(), in, target_file, markers).second();
		
		assertNotNull(file);
		assertEquals(0, markers.size());
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void testProjectDefine() throws CoreException {
		String testname = "testProjectDefine";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS("/data/arg_file_define_proj", fTmpDir);
		
//		fProject = TestUtils.importProject(new File(fTmpDir, "arg_file_define_proj"));
		fProject = TestUtils.createProject("arg_file_define_proj",  
				new File(fTmpDir, "arg_file_define_proj"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
		
		SVProjectFileWrapper wrapper = pdata.getProjectFileWrapper();
		wrapper.addGlobalDefine("ARG_FILE_DEFINE_PROJ", "1");
		pdata.setProjectFileWrapper(wrapper);
		
		SVDBIndexCollection index_collection = pdata.getProjectIndexMgr();
		
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(index_collection, "arg_file_define_proj");
	}

	public void testProjectUndefined() throws CoreException {
		String testname = "testProjectUndefined";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS("/data/arg_file_define_proj", fTmpDir);
		
		fProject = TestUtils.createProject("arg_file_define_proj",  
				new File(fTmpDir, "arg_file_define_proj"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);

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
		String testname = "testProjectDefine_1";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS("/data/arg_file_define_proj_1", fTmpDir);
		
		fProject = TestUtils.createProject("arg_file_define_proj_1",  
				new File(fTmpDir, "arg_file_define_proj_1"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);

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
		String testname = "testArgFilePathChange";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		utils.copyBundleDirToFS("/data/project_settings_proj1", fTmpDir);
		
		fProject = TestUtils.importProject(new File(fTmpDir, "project_settings_proj1"));
		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
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

}
