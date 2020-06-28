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
package net.sf.sveditor.core.tests.project_build;

import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.open_decl.OpenDeclResult;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class TestProjectBuildUBus extends SVCoreTestCaseBase {

	public void testInsertBasicSyntaxError() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBProjectData pd = setupUBusProject();

		String test_lib_sv = "${workspace_loc}/ubus/examples/test_lib.sv";
		SVDBIndexCollection index = pd.getProjectIndexMgr();
		
		Tuple<ISVDBIndex, SVDBFile> fl = findFile(index, test_lib_sv);
		
		
	}
	
	private Tuple<ISVDBIndex, SVDBFile> findFile(SVDBIndexCollection index, String path) {
		List<SVDBSearchResult<SVDBFile>> result = index.findFile(path);
		assertEquals(1, result.size());
	
		return new Tuple<ISVDBIndex, SVDBFile>(result.get(0).getIndex(), result.get(0).getItem());
	}
	
	private StringBuilder readFile(SVDBIndexCollection index, String path) {
		List<SVDBSearchResult<SVDBFile>> result = index.findFile(path);
		assertEquals(1, result.size());
		ISVDBIndex path_i = result.get(0).getIndex();
		
		InputStream in = path_i.getFileSystemProvider().openStream(path);
		assertNotNull(in);
		
		StringBuilder ret = TestUtils.readInputSB(in);
		
		path_i.getFileSystemProvider().closeStream(in);
		
		return ret;
	}
	
	private void writeFile(SVDBIndexCollection index, String path, StringBuilder content) {
		List<SVDBSearchResult<SVDBFile>> result = index.findFile(path);
		assertEquals(1, result.size());
		ISVDBIndex path_i = result.get(0).getIndex();
		
		OutputStream out = path_i.getFileSystemProvider().openStreamWrite(path);
		assertNotNull(out);

//		TestUtils.
//		
//		SVFileUtils.writeToFile(file, content);
//		StringBuilder ret = TestUtils.readInputSB(in);
//		
//		path_i.getFileSystemProvider().closeStream(in);
//		
//		return ret;
	}
	
	
	public void testUBusOutsideWorkspaceFile() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBProjectData pd = setupUBusProject();
		
		SVDBIndexCollection index = pd.getProjectIndexMgr();

		String test_lib_sv = "${workspace_loc}/ubus/examples/test_lib.sv";
		List<SVDBSearchResult<SVDBFile>> result = index.findFile(test_lib_sv);
		assertEquals(1, result.size());
		
		SVDBSearchResult<SVDBFile> r = result.get(0);

		ISVDBFileSystemProvider fs = r.getIndex().getFileSystemProvider();
		InputStream in = fs.openStream(test_lib_sv);
		assertNotNull(in);
		String input = TestUtils.readInput(in);
		fs.closeStream(in);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(input);
		
		int offset = input.indexOf("extends uvm_test");
		offset += "extends u".length();
		scanner.seek(offset);
		
		int line = getLineOfIndex(input, offset);

		Tuple<SVExprContext, ISVDBScopeItem> ctxt_r = 
				OpenDeclUtils.getContextScope(r.getItem(), line, scanner);
		
		List<OpenDeclResult> results = OpenDeclUtils.openDecl(
				ctxt_r.first(), 
				ctxt_r.second(),
				index);
	
		assertEquals(1, results.size());
	}
	
	private int getLineOfIndex(String str, int offset) {
		int line=1, idx=0;
		
		while (idx <= offset) {
			if (str.charAt(idx) == '\n') {
				line++;
			}
			idx++;
		}
		
		return line;
	}
	
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
		
		Job j = new Job("Rebuild Index") {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				pmgr.rebuildProject(new NullProgressMonitor(), p, true);
				return Status.OK_STATUS;
			}
		};
	
		j.schedule();
		try {
			j.join();
		} catch (InterruptedException e) {}

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

}
