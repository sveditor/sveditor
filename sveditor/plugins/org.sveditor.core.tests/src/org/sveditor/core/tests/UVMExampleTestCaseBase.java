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
package org.sveditor.core.tests;

import java.io.File;
import java.io.InputStream;
import java.util.List;

import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.sveditor.core.db.index.SVDBIndexCollection;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.project.SVDBProjectManager;
import org.sveditor.core.db.project.SVProjectFileWrapper;
import org.sveditor.core.db.search.SVDBSearchResult;

public class UVMExampleTestCaseBase extends SVCoreTestCaseBase {

	/**
	 * Creates a project named 'ubus'
	 * 
	 * @return
	 */
	protected SVDBProjectData setupUBusProject() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		File ubus = new File(fTmpDir, "uvm/examples/integrated/ubus");
		
		final IProject p = TestUtils.createProject("ubus", ubus);
		addProject(p);

		final SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
	
		TestUtils.copy(
			"+incdir+${workspace_loc}/ubus/sv\n" +
			"+incdir+${workspace_loc}/ubus/examples\n" +
			"+incdir+../../../src\n" +
			"../../../src/uvm_pkg.sv\n" +
			"${workspace_loc}/ubus/examples/ubus_tb_top.sv\n" +
			"${workspace_loc}/ubus/sv/ubus_version.svh\n",
			p.getFile(new Path("sve.f")));
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/ubus/sve.f");
		pd.setProjectFileWrapper(fw);
		
		Job j = new Job("Rebuild Index") {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				pmgr.rebuildProject(new NullProgressMonitor(), p, true, null);
				return Status.OK_STATUS;
			}
		};
	
		j.schedule();
		try {
			j.join();
		} catch (InterruptedException e) {}

		return pd;
	}
	
	protected String readFile(SVDBIndexCollection index, String path) {
		List<SVDBSearchResult<SVDBFile>> result = index.findFile(path);
		assertEquals(1, result.size());
		
		SVDBSearchResult<SVDBFile> r = result.get(0);

		ISVDBFileSystemProvider fs = r.getIndex().getFileSystemProvider();
		InputStream in = fs.openStream(path);
		assertNotNull(in);
		String input = TestUtils.readInput(in);
		fs.closeStream(in);		
		
		return input;
	}

}
