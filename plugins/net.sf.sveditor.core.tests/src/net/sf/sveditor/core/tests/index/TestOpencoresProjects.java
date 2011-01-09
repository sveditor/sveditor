package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestOpencoresProjects extends TestCase {
	
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
	}
	
	public void testEthernetMac() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testEthernetMac", "/wb_ethmac.zip", "wb_ethmac",
				new String[] {"${workspace_loc}/wb_ethmac/dut.f",
							  "${workspace_loc}/wb_ethmac/bench.f"});
	}
	
	public void testI2C() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testI2C", "/i2c.zip", "i2c",
				new String[] {"${workspace_loc}/i2c/dut.f",
							  "${workspace_loc}/i2c/bench.f"});
	}

	public void testDMA() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testDMA", "/wb_dma.zip", "wb_dma",
				new String[] {"${workspace_loc}/wb_dma/dut.f",
							  "${workspace_loc}/wb_dma/bench.f"});
	}
	
	public void testUSBHostSlave() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testDMA", "/usbhostslave.zip", "usbhostslave",
				new String[] {"${workspace_loc}/usbhostslave/usb.f"});
	}

	private void runTest(
			String				testname,
			String				zipfile_path,
			String				proj_path,
			String				arg_file_paths[]) throws CoreException {
		
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		cleanupWorkspace();

		// Create a new project for the 
		File test_dir = new File(fTmpDir, testname);
		File db_dir = new File(fTmpDir, "db");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		if (db_dir.exists()) {
			assertTrue(db_dir.delete());
		}
		assertTrue(db_dir.mkdirs());
		
		utils.unpackBundleZipToFS(zipfile_path, test_dir);
		File project_path = new File(test_dir, proj_path);
		
		IProject project_dir = TestUtils.createProject(project_path.getName(), project_path);
		
		// Setup appropriate project settings
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Add an argument-file paths
		SVProjectFileWrapper p_wrapper = p_data.getProjectFileWrapper().duplicate();
		if (arg_file_paths != null) {
			for (String arg_file : arg_file_paths) {
				p_wrapper.getArgFilePaths().add(new SVDBPath(arg_file));
				p_wrapper.getArgFilePaths().add(new SVDBPath(arg_file));
			}
		}
		p_data.setProjectFileWrapper(p_wrapper);
		
		SVDBIndexCollectionMgr project_index = p_data.getProjectIndexMgr();
		assertNoErrors(project_index);
		
		// force index loading
		ISVDBItemIterator it = project_index.getItemIterator();
		while (it.hasNext()) {
			it.nextItem();
		}

		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	private void assertNoErrors(ISVDBIndexIterator index_it) {
		ISVDBItemIterator it_i = index_it.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		while (it_i.hasNext()) {
			SVDBItem it = it_i.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem marker = (SVDBMarkerItem)it;
				if (marker.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(marker);
				}
			}
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage() + " @ " + 
					m.getParent().getName() + ":" + m.getLocation().getLine());
		}
		
		assertEquals(0, errors.size());
	}
		

	private void cleanupWorkspace() throws CoreException {
		
		// TODO: close all open projects
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		for (IProject p : root.getProjects()) {
			p.delete(true, new NullProgressMonitor());
		}
	}

}
