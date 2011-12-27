package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestCrossIndexReferences extends TestCase {
	private File				fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		CoreReleaseTests.clearErrors();
	}

	@Override
	protected void tearDown() throws Exception {
//		TestUtils.delete(fTmpDir);
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void testBasicArgFileIndexCrossRef() throws CoreException {
		String testname = "testBasicArgFileIndexCrossRef";
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		IProject p1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/index/arg_file_cross_index_ref/p1");
		
		IProject p2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/index/arg_file_cross_index_ref/p2");
		IProjectDescription p2_desc = p2.getDescription();
		p2_desc.setReferencedProjects(new IProject[] {p1});
		p2.setDescription(p2_desc,  new NullProgressMonitor());

		SVDBProjectData p1_pdata = pmgr.getProjectData(p1);
		SVProjectFileWrapper p1_fwrapper = p1_pdata.getProjectFileWrapper();
		SVDBProjectData p2_pdata = pmgr.getProjectData(p2);
		SVProjectFileWrapper p2_fwrapper = p2_pdata.getProjectFileWrapper();

		p1_fwrapper.addArgFilePath("${workspace_loc}/p1/p1/p1.f");
		p2_fwrapper.addArgFilePath("${workspace_loc}/p2/p2/p2.f");

		p1_pdata.setProjectFileWrapper(p1_fwrapper);
		p2_pdata.setProjectFileWrapper(p2_fwrapper);
	
		SVDBIndexCollectionMgr p1_index = p1_pdata.getProjectIndexMgr();
		SVDBIndexCollectionMgr p2_index = p2_pdata.getProjectIndexMgr();
		
		List<SVDBDeclCacheItem> result = p2_index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"p1_c", SVDBFindDefaultNameMatcher.getDefault());
		
		assertEquals(1, result.size());
		SVDBDeclCacheItem p1_c = result.get(0);
		assertEquals("p1_c", p1_c.getName());
		assertEquals(SVDBItemType.ClassDecl, p1_c.getType());
		assertNotNull(p1_c.getSVDBItem());
	}
	
	public void testCircularArgFileIndexCrossRef() throws CoreException {
		String testname = "testCircularArgFileIndexCrossRef";
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		IProject p1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/index/arg_file_cross_index_ref/p1");
		
		IProject p2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/index/arg_file_cross_index_ref/p2");
		IProjectDescription p2_desc = p2.getDescription();
		p2_desc.setReferencedProjects(new IProject[] {p1});
		p2.setDescription(p2_desc,  new NullProgressMonitor());

		IProjectDescription p1_desc = p1.getDescription();
		p1_desc.setReferencedProjects(new IProject[] {p2});
		p1.setDescription(p1_desc,  new NullProgressMonitor());

		SVDBProjectData p1_pdata = pmgr.getProjectData(p1);
		SVProjectFileWrapper p1_fwrapper = p1_pdata.getProjectFileWrapper();
		SVDBProjectData p2_pdata = pmgr.getProjectData(p2);
		SVProjectFileWrapper p2_fwrapper = p2_pdata.getProjectFileWrapper();

		p1_fwrapper.addArgFilePath("${workspace_loc}/p1/p1/p1.f");
		p2_fwrapper.addArgFilePath("${workspace_loc}/p2/p2/p2.f");

		p1_pdata.setProjectFileWrapper(p1_fwrapper);
		p2_pdata.setProjectFileWrapper(p2_fwrapper);
	
		SVDBIndexCollectionMgr p1_index = p1_pdata.getProjectIndexMgr();
		SVDBIndexCollectionMgr p2_index = p2_pdata.getProjectIndexMgr();
		
		List<SVDBDeclCacheItem> result = p2_index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"p1_c", SVDBFindDefaultNameMatcher.getDefault());
		
		assertEquals(1, result.size());
		SVDBDeclCacheItem p1_c = result.get(0);
		assertEquals("p1_c", p1_c.getName());
		assertEquals(SVDBItemType.ClassDecl, p1_c.getType());
		assertNotNull(p1_c.getSVDBItem());
	}

}
