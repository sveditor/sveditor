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


package net.sf.sveditor.core.tests.index;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestGlobalDefine extends SVCoreTestCaseBase {

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		SVCorePlugin.getDefault().getProjMgr().init();
	}
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
		super.tearDown();
	}

	public void testArgFileIndexGlobalDefine() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		CoreReleaseTests.clearErrors();
		
		IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/basic_lib_global_defs/", project_dir);
		
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		SVProjectFileWrapper fw = p_data.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/project/basic_lib_global_defs/proj.f");
		p_data.setProjectFileWrapper(fw);
		
		int_testGlobalDefine("testArgFileIndexGlobalDefine", p_data, null);
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	private void int_testGlobalDefine(
			String 						testname,
			SVDBProjectData				project_data,
			ISVDBIndex					index) {
		LogHandle log = LogFactory.getLogHandle(testname);
		CoreReleaseTests.clearErrors();
		
		// Add the definition that we'll check for
		SVProjectFileWrapper p_wrap = project_data.getProjectFileWrapper().duplicate();
		p_wrap.getGlobalDefines().add(new Tuple<String, String>("ENABLE_CLASS1", ""));
		project_data.setProjectFileWrapper(p_wrap);
		
		p_wrap = project_data.getProjectFileWrapper();
		assertEquals("Check that define not forgotten", 1, p_wrap.getGlobalDefines().size());
		
		SVDBIndexCollection index_mgr = project_data.getProjectIndexMgr();
		index_mgr.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index_mgr, "class1");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}
}
