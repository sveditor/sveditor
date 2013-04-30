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
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVTestCaseBase;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestOpencoresProjects extends SVTestCaseBase {
	
	private File			fTmpDir;
	private IProject		fProject;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
	
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
			fProject = null;
		}
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}
	
	public void testEthernetMac() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testEthernetMac", "/wb_ethmac.zip", "wb_ethmac",
				new String[] {"${workspace_loc}/wb_ethmac/wb_ethmac.f"});
	}
	
	public void testI2C() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testI2C", "/i2c.zip", "i2c",
				new String[] {"${workspace_loc}/i2c/i2c.f"});
	}

	public void testDMA() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest("testDMA", "/wb_dma.zip", "wb_dma",
				new String[] {"${workspace_loc}/wb_dma/wb_dma.f"});
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
		LogHandle log = LogFactory.getLogHandle(testname);
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
		
		fProject = TestUtils.createProject(project_path.getName(), project_path);
		
		// Setup appropriate project settings
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(fProject);
		
		// Add an argument-file paths
		SVProjectFileWrapper p_wrapper = p_data.getProjectFileWrapper().duplicate();
		if (arg_file_paths != null) {
			for (String arg_file : arg_file_paths) {
				p_wrapper.getArgFilePaths().add(new SVDBPath(arg_file));
				p_wrapper.getArgFilePaths().add(new SVDBPath(arg_file));
			}
		}
		p_data.setProjectFileWrapper(p_wrapper);
		
		SVDBIndexCollection project_index = p_data.getProjectIndexMgr();
		assertNoErrors(log, project_index);
		
		// force index loading
		ISVDBItemIterator it = project_index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		
		IndexTestUtils.assertNoErrWarn(log, project_index);

		assertEquals(0, CoreReleaseTests.getErrors().size());
		project_index.dispose();
		LogFactory.removeLogHandle(log);
	}

	private void assertNoErrors(LogHandle log, ISVDBIndexIterator index_it) {
		ISVDBItemIterator it_i = index_it.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it_i.hasNext()) {
			ISVDBItemBase it = it_i.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarker marker = (SVDBMarker)it;
				if (marker.getMarkerType() == MarkerType.Error) {
					errors.add(marker);
				}
			}
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage() + " @ " + ":" + m.getLocation().getLine());
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
