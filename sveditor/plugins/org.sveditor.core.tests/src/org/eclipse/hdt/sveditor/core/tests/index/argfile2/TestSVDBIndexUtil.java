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
package org.sveditor.core.tests.index.argfile2;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.index.SVDBIndexUtil;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.project.SVDBProjectManager;
import org.sveditor.core.db.project.SVProjectFileWrapper;

import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

public class TestSVDBIndexUtil extends SVCoreTestCaseBase {

	public void testIndexUtilFindFile() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().setTestDebugLevel(0);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		IProject uvm = createProject("uvm", new File(fTmpDir, "uvm"));
		
		TestUtils.copy(
				"+define+QUESTA\n" +
				"+incdir+src\n" +
				"src/uvm_pkg.sv",
				uvm.getFile("uvm.f"));
		
		IFile uvm_pkg_sv = uvm.getFile("src/uvm_pkg.sv");
		
		assertNotNull(uvm_pkg_sv);
		assertTrue(uvm_pkg_sv.exists());

		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(uvm);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/uvm.f");
		pdata.setProjectFileWrapper(fw);
		
		rebuildProject(uvm);
		
		SVDBFile file = SVDBIndexUtil.findIndexFile(uvm_pkg_sv);
	
		assertNotNull(file);
	}
	
}
