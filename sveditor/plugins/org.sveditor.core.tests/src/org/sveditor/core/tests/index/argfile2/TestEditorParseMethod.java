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
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.tests.IndexTestUtils;
import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.SVDBTestUtils;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.BundleUtils;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;

public class TestEditorParseMethod extends SVCoreTestCaseBase {
	
	public void testSFCUIncomingMacros() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/index/sfcu_cross_file_macros", fTmpDir);
		
		File sfcu_cross_file_macros = new File(fTmpDir, "sfcu_cross_file_macros");
		TestUtils.createProject("sfcu_cross_file_macros", sfcu_cross_file_macros);

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"sfcu_cross_file_macros",
				"${workspace_loc}/sfcu_cross_file_macros/sfcu_cross_file_macros.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"pkg1_cls1",
				"pkg1_cls2");
		
		List<SVDBMarker> markers;
		Tuple<SVDBFile, SVDBFile> result;

		// First, test that macros propagate from package down to included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/sfcu_cross_file_macros/pkg1_cls1.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg1_cls1");
		
		// Next, test that macros propagate across included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/sfcu_cross_file_macros/pkg2_cls2.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg2_cls2");
	}

	public void testMFCUIncomingMacros() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/index/mfcu_cross_file_macros", fTmpDir);
		
		File mfcu_cross_file_macros = new File(fTmpDir, "mfcu_cross_file_macros");
		TestUtils.createProject("mfcu_cross_file_macros", mfcu_cross_file_macros);

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"mfcu_cross_file_macros",
				"${workspace_loc}/mfcu_cross_file_macros/mfcu_cross_file_macros.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"pkg1_cls1",
				"pkg1_cls2");
		
		List<SVDBMarker> markers;
		Tuple<SVDBFile, SVDBFile> result;

		// First, test that macros propagate from package down to included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/mfcu_cross_file_macros/pkg1_cls1.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg1_cls1");
		
		// Next, test that macros propagate across included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/mfcu_cross_file_macros/pkg2_cls2.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg2_cls2");
	}
	
	public void testIncludedDeclarationsNotIncluded() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		
		utils.copyBundleDirToFS("/data/index/mfcu_cross_file_macros", fTmpDir);
		
		IProject p = TestUtils.createProject("included_decl", 
				new File(fTmpDir, "included_decl"));
		addProject(p);
		
		SVFileUtils.copy(
				"top.sv",
				p.getFile("included_decl.f"));
		
		SVFileUtils.copy(
				"function void my_func();\n" +
				"endfunction\n",
				p.getFile("params.svh"));
		
		SVFileUtils.copy(
				"module top;\n" +
				"`include \"params.svh\"\n" +
				"\n" +
				"function in_top;\n" +
				"endfunction\n" +
				"endmodule\n",
				p.getFile("top.sv"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"included_decl",
				"${workspace_loc}/included_decl/included_decl.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.loadIndex(new NullProgressMonitor());
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
	
		SVDBFile file = index.findFile("${workspace_loc}/included_decl/top.sv");
		SVDBTestUtils.assertFileHasElements(file, "top", "in_top");
		SVDBTestUtils.assertFileDoesNotHaveElements(file, "my_func");
	
		// Now, check the return of the index parse method
		InputStream in = index.getFileSystemProvider().openStream(
				"${workspace_loc}/included_decl/top.sv");
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> parse_r = index.parse(new NullProgressMonitor(), in, 
				"${workspace_loc}/included_decl/top.sv",
				markers);
		
		SVDBTestUtils.assertFileHasElements(parse_r.second(), "top", "in_top");
		SVDBTestUtils.assertFileDoesNotHaveElements(parse_r.second(), "my_func");
		
		index.getFileSystemProvider().closeStream(in);
	}

	public void testMultiIncludeGuardsIgnoredOnReparse() {
		SVCorePlugin.getDefault().enableDebug(false);

		IProject p = TestUtils.createProject("multi_include_guards", 
				new File(fTmpDir, "multi_include_guards"));
		addProject(p);
		
		SVFileUtils.copy(
				"top_pkg.sv",
				p.getFile("multi_include_guards.f"));
		
		SVFileUtils.copy(
				"package top_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"endpackage\n",
				p.getFile("top_pkg.sv"));
		
		SVFileUtils.copy(
				"`ifndef INCLUDED_CLS1_SVH\n" +
				"`define INCLUDED_CLS1_SVH\n" +
				"	class cls1;\n" +
				"	endclass\n" +
				"`endif /* INCLUDED_CLS1_SVH */\n",
				p.getFile("cls1.svh"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"included_decl",
				"${workspace_loc}/multi_include_guards/multi_include_guards.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.loadIndex(new NullProgressMonitor());
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
	
//		SVDBFile file = index.findFile("${workspace_loc}/included_decl/top.sv");
//		SVDBTestUtils.assertFileHasElements(file, "top", "in_top");
//		SVDBTestUtils.assertFileDoesNotHaveElements(file, "my_func");
		
		IndexTestUtils.assertFileHasElements(index, "cls1");
	
		// Now, check the return of the index parse method
		InputStream in = index.getFileSystemProvider().openStream(
				"${workspace_loc}/multi_include_guards/cls1.svh");
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> parse_r = index.parse(new NullProgressMonitor(), in, 
				"${workspace_loc}/multi_include_guards/cls1.svh",
				markers);
		
		SVDBTestUtils.assertFileHasElements(parse_r.second(), "cls1");
		
		index.getFileSystemProvider().closeStream(in);
	}
}


