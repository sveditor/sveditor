package net.sf.sveditor.core.tests.project_settings;

import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class ProjectSettingsTests extends SVCoreTestCaseBase {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ProjectSettingsTests");
		s.addTest(new TestSuite(ProjectSettingsTests.class));
		s.addTest(new TestSuite(TestProjectSettingsVarRefs.class));
		s.addTest(new TestSuite(TestProjectSettingChanges.class));
		return s;
	}
	
	/**
	 * Test that correct results are seen when we change the source collection
	 * specified for a project
	 */
	public void testSourceCollectionChange() {
		IProject fProject = TestUtils.createProject("src_collection", fTmpDir);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToWS("/data/project_settings/src_collection_1", fProject);
		
		SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
		
		SVProjectFileWrapper fw;
		SVDBSourceCollection sc;
		SVDBIndexCollection index;
		
		fw = pd.getProjectFileWrapper();
		sc = new SVDBSourceCollection("${workspace_loc}/src_collection/src_collection_1/subdir_1", true);
		fw.getSourceCollections().clear();
		fw.getSourceCollections().add(sc);
		
		pd.setProjectFileWrapper(fw, true);
		
		index = pd.getProjectIndexMgr();
		
		IndexTestUtils.assertFileHasElements(index, "class_1");
		IndexTestUtils.assertDoesNotContain(index,  "class_2");
		
		fw = pd.getProjectFileWrapper();
		sc = new SVDBSourceCollection("${workspace_loc}/src_collection/src_collection_1/subdir_2", true);
		fw.getSourceCollections().clear();
		fw.getSourceCollections().add(sc);
		
		pd.setProjectFileWrapper(fw, true);
		
		index = pd.getProjectIndexMgr();
		
		IndexTestUtils.assertFileHasElements(index, "class_2");
		IndexTestUtils.assertDoesNotContain(index,  "class_1");
	}
	
	/**
	 * Test that if we change
	 */
	public void testSourceCollectionChangeIncExclExts() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject fProject = TestUtils.createProject("src_collection", fTmpDir);
		addProject(fProject);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToWS("/data/project_settings/src_collection_2", fProject);
		
		SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);
		
		SVProjectFileWrapper fw;
		SVDBSourceCollection sc;
		SVDBIndexCollection index;
		
		fw = pd.getProjectFileWrapper();
		sc = new SVDBSourceCollection("${workspace_loc}/src_collection/src_collection_2", false);
		sc.getIncludes().add("*.sv");
		fw.getSourceCollections().clear();
		fw.getSourceCollections().add(sc);
		
		pd.setProjectFileWrapper(fw, true);
		
		index = pd.getProjectIndexMgr();
		
		IndexTestUtils.assertFileHasElements(index, "class_1");
		IndexTestUtils.assertDoesNotContain(index,  "class_2");
		
		fw = pd.getProjectFileWrapper();
		sc = new SVDBSourceCollection("${workspace_loc}/src_collection/src_collection_2", false);
		sc.getIncludes().add("*.svh");
		fw.getSourceCollections().clear();
		fw.getSourceCollections().add(sc);
		
		pd.setProjectFileWrapper(fw, true);
		
		index = pd.getProjectIndexMgr();
		
		IndexTestUtils.assertFileHasElements(index, "class_2");
		IndexTestUtils.assertDoesNotContain(index,  "class_1");
	}
}
