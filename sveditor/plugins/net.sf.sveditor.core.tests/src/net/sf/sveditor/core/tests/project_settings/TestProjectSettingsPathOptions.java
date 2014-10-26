package net.sf.sveditor.core.tests.project_settings;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.SVMarkers;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class TestProjectSettingsPathOptions extends SVCoreTestCaseBase {

	
	public void testWorkspaceRelFilesFSPath() throws CoreException, IOException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(true);

		utils.copyBundleDirToFS("/data/project_settings_rel_inc_proj1", fTmpDir);
		
		File proj = new File(fTmpDir, "project_settings_rel_inc_proj1");
		
		IProject project = TestUtils.createProject(proj.getName(), proj);
		addProject(project);
	
		SVCorePlugin.setenv("PROJ_TMPDIR", fTmpDir.getAbsolutePath());

		SVDBProjectData pdata = SVCorePlugin.getDefault().getProjMgr().getProjectData(project);
		SVDBIndexCollection index_collection = null;
		SVProjectFileWrapper fw;
		
		CoreReleaseTests.clearErrors();
		fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${PROJ_TMPDIR}/" + proj.getName() + "/top_dir/files.f");
		pdata.setProjectFileWrapper(fw, true);
		
		index_collection = pdata.getProjectIndexMgr();
		index_collection.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index_collection);
		
		// Ensure that there are now no errors
		assertTrue(CoreReleaseTests.getErrors().size() == 0);		
	}

}
