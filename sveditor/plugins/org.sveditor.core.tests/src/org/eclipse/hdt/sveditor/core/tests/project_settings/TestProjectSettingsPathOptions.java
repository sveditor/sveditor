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
package org.sveditor.core.tests.project_settings;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.tests.CoreReleaseTests;
import org.sveditor.core.tests.IndexTestUtils;
import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.SVMarkers;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.SVDBIndexCollection;
import org.sveditor.core.db.index.SVDBIndexUtil;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.project.SVProjectFileWrapper;
import org.sveditor.core.db.search.SVDBSearchResult;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

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
