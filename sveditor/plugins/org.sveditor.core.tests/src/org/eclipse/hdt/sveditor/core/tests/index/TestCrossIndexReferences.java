/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.tests.CoreReleaseTests;
import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;

public class TestCrossIndexReferences extends SVCoreTestCaseBase {
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		CoreReleaseTests.clearErrors();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
	}

	@Override
	protected void tearDown() throws Exception {
		StringBuilder sb = new StringBuilder();
		for (Exception err : CoreReleaseTests.getErrors()){
			sb.append(err.getMessage() + " ");
		}
		assertEquals(sb.toString(), 0, CoreReleaseTests.getErrors().size());
		super.tearDown();
	}

	public void testBasicArgFileIndexCrossRef() throws CoreException {
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		IProject p1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/index/arg_file_cross_index_ref/p1");
		addProject(p1);
		
		IProject p2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/index/arg_file_cross_index_ref/p2");
		addProject(p2);
		
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
	
		SVDBIndexCollection p1_index = p1_pdata.getProjectIndexMgr();
		SVDBIndexCollection p2_index = p2_pdata.getProjectIndexMgr();
		p1_index.loadIndex(new NullProgressMonitor());
		p2_index.loadIndex(new NullProgressMonitor());
	
		IndexTestUtils.assertFileHasElements(fLog, p2_index, "p1_c");
	}
	
	public void testCircularArgFileIndexCrossRef() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		IProject p1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/index/arg_file_cross_index_ref/p1");
		addProject(p1);
		
		IProject p2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/index/arg_file_cross_index_ref/p2");
		addProject(p2);
		
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
	
		SVDBIndexCollection p1_index = p1_pdata.getProjectIndexMgr();
		SVDBIndexCollection p2_index = p2_pdata.getProjectIndexMgr();
		p1_index.loadIndex(new NullProgressMonitor());
		p2_index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, p2_index, "p1_c");
	}

	public void testIteratorCircularArgFileIndexCrossRef() throws CoreException {
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		IProject p1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/index/arg_file_cross_index_ref/p1");
		addProject(p1);
		
		IProject p2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/index/arg_file_cross_index_ref/p2");
		addProject(p2);
		
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
	
		SVDBIndexCollection p1_index = p1_pdata.getProjectIndexMgr();
		SVDBIndexCollection p2_index = p2_pdata.getProjectIndexMgr();
		p1_index.loadIndex(new NullProgressMonitor());
		p2_index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, p2_index, "p1_c", "p2_c");
	}

}
