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
package org.eclipse.hdt.sveditor.core.tests.parser.perf;

import java.io.File;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexStats;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;

public class TestUVMParsePerformance extends SVCoreTestCaseBase {

	private SVDBProjectData setupUBusProject() {
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
		


//		boolean build_res = false;
//
//		for (int i=0; i<16; i++) {
//			build_res = pmgr.rebuildProject(new NullProgressMonitor(), p, false);
//			if (build_res) {
//				break;
//			}
//		}
//		
//		assertTrue(build_res);
		
		return pd;
	}
	
	public void testUBusParsePerformance() {
		SVCorePlugin.setTestModeBuilderDisabled();
		
		SVDBProjectData pd = setupUBusProject();
		final SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		final IProject p = fProjectList.get(0);

		int n_rebuilds = 20;
		ISVDBIndex index = null;
		for (ISVDBIndex i : pd.getProjectIndexMgr().getIndexList()) {
			if (i.getBaseLocation().contains("ubus")) {
				index = i;
				break;
			}
		}
		
		System.out.println("baseLocation: " + index.getBaseLocation());
		long parse_time = 0;
		long decl_cache_time = 0;
		long ref_cache_time = 0;
		long preproc_time = 0;
		long start = System.currentTimeMillis();
		for (int i=0; i<n_rebuilds; i++) {
			index.execIndexChangePlan(new NullProgressMonitor(), 
					new SVDBIndexChangePlanRebuild(index));
			SVDBIndexStats stats = ((SVDBArgFileIndex)index).getIndexStats();
			parse_time += stats.getLastIndexParseTime();
			decl_cache_time += stats.getLastIndexDeclCacheTime();
			ref_cache_time += stats.getLastIndexRefCacheTime();
			preproc_time += stats.getLastIndexPreProcessTime();
		}
		long end = System.currentTimeMillis();
		
		System.out.println("n_rebuilds: " + n_rebuilds + " total time: " + (end-start) + 
				" time/rebuild: " + (end-start)/n_rebuilds);
		System.out.println("parse_time: " + parse_time);
		System.out.println("preproc_time: " + preproc_time);
		System.out.println("decl_cache_time: " + decl_cache_time);
		System.out.println("ref_cache_time: " + ref_cache_time);
	}

}
