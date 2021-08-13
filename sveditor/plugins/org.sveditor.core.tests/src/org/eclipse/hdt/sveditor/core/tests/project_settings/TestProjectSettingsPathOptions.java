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

public class TestProjectSettingsPathOptions extends SVCoreTestCaseBase {

	
	public void testWorkspaceRelFilesFSPath() throws CoreException, IOException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);

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
