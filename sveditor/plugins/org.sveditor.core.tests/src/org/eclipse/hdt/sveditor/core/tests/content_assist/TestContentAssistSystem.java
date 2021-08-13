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
package org.eclipse.hdt.sveditor.core.tests.content_assist;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFileOverrideIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexUtil;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestContentAssistSystem extends SVCoreTestCaseBase {
	private BundleUtils			fUtils;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fUtils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
	}

	public void testGlobalFieldRef() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
			"class c1;\n" +
			"	function void foo;\n" +
			"		field_c<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		
		IProject fProject = TestUtils.createProject("project");
		addProject(fProject);
		
		fUtils.copyBundleDirToWS("/data/content_assist/global_field_ref/", fProject);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/global_field_ref/global_field_ref.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));

		ContentAssistTests.runTest(testname, doc, index, 
				"field_cls");
	}
	
	public void disabled_testShadowSVBuiltinProjectFile() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	int				my_q[$];\n" +
			"	function void foo;\n" +
			"		my_q.s<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		IProject fProject = TestUtils.createProject("project");
		addProject(fProject);
		
		fUtils.copyBundleDirToWS("/data/content_assist/simple_proj/", fProject);
		
		TestUtils.copy(
				"class c1;\n" +
				"endclass\n",
				fProject.getFile("simple_proj/c1.svh"));

		Tuple<ISVDBIndex, SVDBIndexCollection> result = SVDBIndexUtil.findIndexFile(
				"${workspace_loc}/project/simple_proj/c1.svh", 
				"project", 
				true);
		
		assertNotNull(result);
		assertNotNull(result.first());
		assertNotNull(result.second());
		
		ContentAssistTests.runTest(testname, doc, result.second(), 
				"size");
	}

	public void disabled_testShadowSVBuiltinNonProjectFile() {
		String testname = "testShadowSVBuiltinNonProjectFile";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	int				my_q[$];\n" +
			"	function void foo;\n" +
			"		my_q.s<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		fUtils.copyBundleDirToWS("/data/content_assist/simple_proj/", project);
	
		File c1 = new File(fTmpDir, "c1.svh");
		TestUtils.copy(
				"class c1;\n" +
				"endclass\n",
				c1);

		Tuple<ISVDBIndex, SVDBIndexCollection> result = SVDBIndexUtil.findIndexFile(
				c1.getAbsolutePath(),
				null,
				true);
		
		assertNotNull(result);
		assertNotNull(result.first());
		assertNotNull(result.second());
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = new SVDBFile(c1.getAbsolutePath());
		
		SVDBFileOverrideIndex index = new SVDBFileOverrideIndex(
				file, null, result.first(), result.second(), markers);
		
		ContentAssistTests.runTest(testname, doc, index, "size");
		
		LogFactory.removeLogHandle(log);		
	}

	public void testUvmEnumerator() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	function void foo;\n" +
			"		int a;\n" +
			"		a = UVM_ME<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File pdir = new File(fTmpDir, "pdir");
		utils.unpackBundleZipToFS("/uvm.zip", pdir);
		
		PrintStream argfile = new PrintStream(new File(pdir, "argfile.f"));
		argfile.println("+define+QUESTA");
		argfile.println("+incdir+./uvm/src");
		argfile.println("./uvm/src/uvm_pkg.sv");
		
		argfile.close();
		
		IProject project = TestUtils.createProject("pdir", pdir);
		addProject(project);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/argfile.f");
		pdata.setProjectFileWrapper(fw, true);
	
		/*
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
				"pdir", "${workspace_loc}/pdir/argfile.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
		 */
		SVDBIndexCollection index = pdata.getProjectIndexMgr();

		index.loadIndex(new NullProgressMonitor());
	
		/*
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = new SVDBFile(c1.getAbsolutePath());
		
		SVDBFileOverrideIndex index = new SVDBFileOverrideIndex(
				file, null, result.first(), result.second(), markers);
		 */

		
		ContentAssistTests.runTest(getName(), doc, index, 
				"uvm_mem_mam",
				"uvm_mem_region",
				"uvm_mem_mam_policy",
				"uvm_mem_mam_cfg",
				"uvm_mem",
				"uvm_mem_single_walk_seq",
				"uvm_mem_walk_seq",
				"uvm_mem_single_access_seq",
				"uvm_mem_access_seq",
				"uvm_mem_shared_access_seq",
				"UVM_MEDIUM",
				"UVM_MEM",
				"uvm_mem_cb",
				"uvm_mem_cb_iter",
				"UVM_MESSAGE_DEFINES_SVH",
				"UVM_MEM_MAM__SV"
				);
	}
	
	public void testUvmEnumerator_2() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	function void foo;\n" +
			"		int a;\n" +
			"		a = UVM_MED<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File pdir = new File(fTmpDir, "pdir");
		utils.unpackBundleZipToFS("/uvm.zip", pdir);
		
		PrintStream argfile = new PrintStream(new File(pdir, "argfile.f"));
		argfile.println("+incdir+./uvm/src");
		argfile.println("./uvm/src/uvm_pkg.sv");
		
		argfile.close();
		
		IProject project = TestUtils.createProject("pdir", pdir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/argfile.f");
		pdata.setProjectFileWrapper(fw);
		
		SVDBIndexCollection index = pdata.getProjectIndexMgr();
		index.loadIndex(new NullProgressMonitor());
	
		/*
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = new SVDBFile(c1.getAbsolutePath());
		
		SVDBFileOverrideIndex index = new SVDBFileOverrideIndex(
				file, null, result.first(), result.second(), markers);
		 */
		
		ContentAssistTests.runTest(getName(), doc, index,
				"UVM_MEDIUM");
	}	

	public void testUvmEnumerator_3() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	function void foo;\n" +
			"		int a;\n" +
			"		a = UVM_MED<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File pdir = new File(fTmpDir, "pdir");
		utils.unpackBundleZipToFS("/uvm.zip", pdir);
		
		PrintStream argfile = new PrintStream(new File(pdir, "argfile.f"));
		argfile.println("+incdir+./uvm/src");
		argfile.println("./uvm/src/uvm_pkg.sv");
		
		argfile.close();
		
		IProject project = TestUtils.createProject("pdir", pdir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/pdir/argfile.f");
		pdata.setProjectFileWrapper(fw);
		
		pdata.getProjectIndexMgr().loadIndex(new NullProgressMonitor());
		
		ISVDBIndex index = null;
		
		for (ISVDBIndex index_i : pdata.getProjectIndexMgr().getIndexList()) {
			fLog.debug("index: " + index_i.getBaseLocation());
			if (index_i.getBaseLocation().equals("${workspace_loc}/pdir/argfile.f")) {
				index = index_i;
				break;
			}
		}
	
		assertNotNull(index);
		
		ContentAssistTests.runTest(getName(), doc, 
				index,
				"UVM_MEDIUM");
	}	

	public void testUvmEnumerator_4() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class c1;\n" +
			"	function void foo;\n" +
			"		int a;\n" +
			"		a = UVM_ME<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File pdir = new File(fTmpDir, "pdir");
		utils.unpackBundleZipToFS("/uvm.zip", pdir);
		
		PrintStream argfile = new PrintStream(new File(pdir, "argfile.f"));
		argfile.println("+define+QUESTA");
		argfile.println("+incdir+./uvm/src");
		argfile.println("./uvm/src/uvm_pkg.sv");
		
		argfile.close();
		
		IProject project = TestUtils.createProject("pdir", pdir);
		addProject(project);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/pdir/argfile.f");
		pdata.setProjectFileWrapper(fw);
		
		pdata.getProjectIndexMgr().loadIndex(new NullProgressMonitor());
		
		ISVDBIndex index = null;
		
		for (ISVDBIndex index_i : pdata.getProjectIndexMgr().getIndexList()) {
			fLog.debug("index: " + index_i.getBaseLocation());
			if (index_i.getBaseLocation().equals("${workspace_loc}/pdir/argfile.f")) {
				index = index_i;
				break;
			}
		}
	
		assertNotNull(index);
		
		ContentAssistTests.runTest(getName(), doc, 
				index,
				"UVM_MEM", "UVM_MEM_MAM__SV",
				"UVM_MESSAGE_DEFINES_SVH",
				"uvm_mem", "uvm_mem_access_seq",
				"uvm_mem_cb", "uvm_mem_cb_iter",
				"uvm_mem_mam", "uvm_mem_mam_cfg",
				"uvm_mem_mam_policy", "uvm_mem_region",
				"uvm_mem_shared_access_seq",
				"uvm_mem_single_access_seq",
				"uvm_mem_single_walk_seq",
				"uvm_mem_walk_seq",
				"UVM_MEDIUM");
	}
}
