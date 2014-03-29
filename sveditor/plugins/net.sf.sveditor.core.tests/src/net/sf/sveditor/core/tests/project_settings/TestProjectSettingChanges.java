package net.sf.sveditor.core.tests.project_settings;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestProjectSettingChanges extends SVCoreTestCaseBase {
	private SVDBProjectManager		fProjMgr;
	
	protected void setUp() throws Exception {
		super.setUp();
		
		fProjMgr = SVCorePlugin.getDefault().getProjMgr();
	}
	
	public void testRemoveErrorIndex() {
		SVCorePlugin.getDefault().enableDebug(false);
		List<SVDBMarker> markers;
		IProject p = TestUtils.createProject("error_index");
		addProject(p);
		
		String error_argfile = 
				"missing_file1.sv\n" +
				"subdir/missing_file2.sv\n"
				;
		
		String okay_argfile = 
				"file1.sv\n"
				;
		
		String file1_sv =
				"`include \"missing_file.svh\"\n" +
				"module m1;\n" +
				"endmodule\n"
				;
		
		TestUtils.copy(error_argfile, 
				p.getFile("error_argfile.f"));
		
		TestUtils.copy(okay_argfile,
				p.getFile("okay_argfile.f"));
		
		TestUtils.copy(file1_sv,
				p.getFile("file1.sv"));
	
		SVDBProjectData pdata = fProjMgr.getProjectData(p);
		SVDBIndexCollection p_index = pdata.getProjectIndexMgr();
		
		SVProjectFileWrapper w;
		
		w = pdata.getProjectFileWrapper();
		w.addArgFilePath("${workspace_loc}/error_index/error_argfile.f");
		
		pdata.setProjectFileWrapper(w);
	
		CoreReleaseTests.clearErrors();
		p_index.rebuildIndex(new NullProgressMonitor());
		p_index.loadIndex(new NullProgressMonitor());
		
		// Ensure that we see errors
//		assertTrue(CoreReleaseTests.getErrors().size() > 0);
		markers = p_index.getMarkers("${workspace_loc}/error_index/error_argfile.f");
		assertNotNull(markers);
		assertTrue((markers.size() > 0));
	
		// Now, update the index settings and ensure that 
		// no errors are seen
		CoreReleaseTests.clearErrors();
		
		w = pdata.getProjectFileWrapper();
		w.getArgFilePaths().clear();
		w.addArgFilePath("${workspace_loc}/error_index/okay_argfile.f");
		pdata.setProjectFileWrapper(w);
		
//		p_index.rebuildIndex(new NullProgressMonitor());
		fIndexRgy.rebuildIndex(
				new NullProgressMonitor(), 
				p.getName());
		p_index.loadIndex(new NullProgressMonitor());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testRemoveErrorIndex_2() throws CoreException {
		String testname = "testRemoveErrorIndex_2";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject p = TestUtils.createProject("error_index");
		addProject(p);
		
		String okay_argfile = 
				"file1.sv\n"
				;
		
		String file1_sv =
//				"`include \"missing_file.svh\"\n" +
				"module m1;\n" +
				"endmodule\n"
				;
		
		String file2_sv =
//				"`include \"missing_file.svh\"\n" +
				"module m2;\n" +
				"endmodule\n"
				;
		
		TestUtils.copy(okay_argfile,
				p.getFile("okay_argfile.f"));
		
		TestUtils.copy(file1_sv,
				p.getFile("file1.sv"));
	
		p.getFolder("subdir").create(
				true, true, new NullProgressMonitor());
		
		TestUtils.copy(file2_sv,
				p.getFile("subdir/file2.sv"));
	
		SVDBProjectData pdata = fProjMgr.getProjectData(p);
		SVDBIndexCollection p_index = pdata.getProjectIndexMgr();
		
		SVProjectFileWrapper w;
		
		w = pdata.getProjectFileWrapper();
		w.getLibraryPaths().add(
				new SVDBPath("c:\\foo\\bar\\missing\\dir"));
		
		pdata.setProjectFileWrapper(w);
	
		CoreReleaseTests.clearErrors();
		p_index.rebuildIndex(new NullProgressMonitor());
		p_index.loadIndex(new NullProgressMonitor());
		
		// Ensure that we see errors
		assertTrue(CoreReleaseTests.getErrors().size() > 0);
	
		// Now, update the index settings and ensure that 
		// no errors are seen
		CoreReleaseTests.clearErrors();
		
		w = pdata.getProjectFileWrapper();
		w.getLibraryPaths().clear();
		w.getArgFilePaths().clear();
		w.addArgFilePath("${workspace_loc}/error_index/okay_argfile.f");
		pdata.setProjectFileWrapper(w);
		
		fIndexRgy.rebuildIndex(
				new NullProgressMonitor(), 
				p.getName());
		p_index.loadIndex(new NullProgressMonitor());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		for (ISVDBIndex i : fIndexRgy.getAllProjectLists()){
			log.debug("Index: " + i.getBaseLocation());
		}
		
		// Expect the project index plus the built-in index
		assertEquals(2, fIndexRgy.getAllProjectLists().size());
		assertEquals(1, fIndexRgy.getProjectIndexList("error_index").size());
	}

}
