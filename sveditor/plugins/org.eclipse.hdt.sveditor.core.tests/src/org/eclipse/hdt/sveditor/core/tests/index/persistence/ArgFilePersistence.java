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


package org.eclipse.hdt.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexInt;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexChangeEvent;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.persistence.DBFormatException;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByName;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.preproc.ISVPreProcessor;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcOutput;

public class ArgFilePersistence extends SVCoreTestCaseBase 
	implements ISVDBIndexChangeListener {
	
	private int						fIndexRebuilt;
	private SVCorePlugin			fCorePlugin;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fCorePlugin = SVCorePlugin.getDefault();
		
		SVCorePlugin.setTestMode();
	}
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();

		super.tearDown();
	}
	
	public void testXbusTransferFileParse() throws DBFormatException {
		String testname = "testXbusTransferFileParse";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		File test_dir = new File(fTmpDir, testname);
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();

		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");

		IProject project = TestUtils.createProject("xbus", xbus);
		addProject(project);

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);

		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		IndexTestUtils.assertNoErrWarn(log, target_index);

		String path = "${workspace_loc}/xbus/sv/xbus_transfer.sv";
		ISVDBFileSystemProvider fs = target_index.getFileSystemProvider();
		target_index.loadIndex(new NullProgressMonitor());
		ISVPreProcessor pp = ((ISVDBIndexInt)target_index).createPreProcScanner(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		InputStream in = fs.openStream(path);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		log.debug("--> Parse 1");
		SVDBFile file = target_index.parse(new NullProgressMonitor(), in, path, markers).second();
		log.debug("<-- Parse 1");
		
		SVPreProcOutput pp_out = pp.preprocess();

		StringBuilder tmp = new StringBuilder();
		// Display the 
		int line=1, ch;
		tmp.append("" + line + ": ");
		while ((ch = pp_out.get_ch()) != -1) {
			tmp.append((char)ch);
			bos.write((char)ch);
			if (ch == '\n') {
				line++;
				tmp.append("" + line + ": ");
			}
		}
		log.debug(tmp.toString());
		
		in = new ByteArrayInputStream(bos.toByteArray());
		log.debug("--> parse()");
		file = target_index.parse(new NullProgressMonitor(), in, path, null).second();
		log.debug("<-- parse()");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		LogFactory.removeLogHandle(log);
	}

	public void testOvmWarningUnbalancedParen() throws DBFormatException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testOvmWarningUnbalancedParen";
		LogHandle log = LogFactory.getLogHandle(testname);
		
		File test_dir = new File(fTmpDir, testname);
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		log.debug("test_dir: " + test_dir.getAbsolutePath());

		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		utils.copyBundleDirToFS("/data/ovm_warning_unbalanced_paren", test_dir);
		File test_proj = new File(test_dir, "ovm_warning_unbalanced_paren");
		
		assertTrue(test_proj.isDirectory());

		IProject project = TestUtils.createProject(test_proj.getName(), test_proj);
		addProject(project);
//		SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);

		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ovm_warning_unbalanced_paren/ovm_warning_unbalanced_paren.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		log.debug("--> loadIndex");
		target_index.loadIndex(new NullProgressMonitor());
		log.debug("<-- loadIndex");
		
		log.debug("--> fileList");
		Iterable<String> file_list = target_index.getFileList(new NullProgressMonitor());
		for (String file : file_list) {
			log.debug("File: " + file);
		}
		log.debug("<-- fileList");
		
		String path = "${workspace_loc}/ovm_warning_unbalanced_paren/ovm_warning_unbalanced_paren.svh";
		ISVDBFileSystemProvider fs = ((ISVDBIndex)target_index).getFileSystemProvider();
		ISVPreProcessor pp = ((ISVDBIndexInt)target_index).createPreProcScanner(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		InputStream in = fs.openStream(path);

		log.debug("--> Parse 1");
		Tuple<SVDBFile, SVDBFile> result = target_index.parse(new NullProgressMonitor(), in, path, null);
	
		SVDBFile file = null;
		if (result != null) {
			file = result.second();
			
		}
		log.debug("<-- Parse 1");
		
		SVPreProcOutput pp_out = pp.preprocess();

		StringBuilder tmp = new StringBuilder();
		// Display the 
		int line=1, ch;
		tmp.append("" + line + ": ");
		while ((ch = pp_out.get_ch()) != -1) {
			tmp.append((char)ch);
			bos.write((char)ch);
			if (ch == '\n') {
				line++;
				tmp.append("" + line + ": ");
			}
		}
		log.debug(tmp.toString());
		
		in = new ByteArrayInputStream(bos.toByteArray());
		log.debug("--> parse()");
		Tuple<SVDBFile, SVDBFile> parse_res = 
				target_index.parse(new NullProgressMonitor(), in, path, null);
		
		assertNotNull(parse_res);
		
		if (result != null) {
			file = parse_res.second();
		}

		log.debug("<-- parse()");
		
		SVDBTestUtils.assertNoErrWarn(file);

		IndexTestUtils.assertNoErrWarn(log, target_index);

		LogFactory.removeLogHandle(log);
	}
	
	public void testOvmErrorUnbalancedParen() throws DBFormatException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testOvmErrorUnbalancedParen";
		LogHandle log = LogFactory.getLogHandle(testname);
		
		File test_dir = new File(fTmpDir, testname);
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		log.debug("test_dir: " + test_dir.getAbsolutePath());

		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		utils.copyBundleDirToFS("/data/ovm_error_unbalanced_paren", test_dir);
		File test_proj = new File(test_dir, "ovm_error_unbalanced_paren");
		
		assertTrue(test_proj.isDirectory());

		IProject project = TestUtils.createProject(test_proj.getName(), test_proj);
		addProject(project);
//		SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(fProject);

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);

		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ovm_error_unbalanced_paren/ovm_error_unbalanced_paren.f",
				SVDBArgFileIndexFactory.TYPE, null);
		target_index.loadIndex(new NullProgressMonitor());
		
		
		String path = "${workspace_loc}/ovm_error_unbalanced_paren/ovm_error_unbalanced_paren.svh";
		ISVDBFileSystemProvider fs = target_index.getFileSystemProvider();
		ISVPreProcessor pp = ((ISVDBIndexInt)target_index).createPreProcScanner(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		InputStream in = fs.openStream(path);
		
		Tuple<SVDBFile, SVDBFile> result = target_index.parse(new NullProgressMonitor(), in, path, null);
		
		assertNotNull(result);

		log.debug("--> Parse 1");
		SVDBFile file = result.second();
		log.debug("<-- Parse 1");
		
		SVPreProcOutput pp_out = pp.preprocess();

		StringBuilder tmp = new StringBuilder();
		// Display the 
		int line=1, ch;
		tmp.append("" + line + ": ");
		while ((ch = pp_out.get_ch()) != -1) {
			tmp.append((char)ch);
			bos.write((char)ch);
			if (ch == '\n') {
				line++;
				tmp.append("" + line + ": ");
			}
		}
		log.debug("PreProcessed Info:\n" + tmp.toString());
		
		in = new ByteArrayInputStream(bos.toByteArray());
		log.debug("--> parse()");
		file = target_index.parse(new NullProgressMonitor(), in, path, null).second();
		log.debug("<-- parse()");
		
		SVDBTestUtils.assertNoErrWarn(file);

		IndexTestUtils.assertNoErrWarn(log, target_index);

		LogFactory.removeLogHandle(log);
	}	

	public void disabled_testWSArgFileTimestampChanged() {
		SVCorePlugin.getDefault().enableDebug(false);
		ByteArrayOutputStream	 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSArgFileTimestampChanged");
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project);
		
		SVDBIndexRegistry rgy = fCorePlugin.getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());

		IndexTestUtils.assertNoErrWarn(log, index);

		SVDBFindByName finder = new SVDBFindByName(index);
		List<ISVDBItemBase> items_1 = finder.findItems("class1", true);
	
		assertEquals(1, items_1.size());
		assertEquals("class1", SVDBItem.getName(items_1.get(0)));
		
		rgy.close();

		// Now, reset the registry
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		log.debug("[NOTE] pre-sleep");
		try {
//			Thread.sleep(2000);
			Thread.sleep(1500);
		} catch (InterruptedException e) {
			log.error("Interruped");
			e.printStackTrace();
		}
//		fCorePlugin.enableDebug(false);
		log.debug("[NOTE] post-sleep");

		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project.getFile(new Path("basic_lib_project/class1_2.svh")));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project.getFile(new Path("basic_lib_project/basic_lib.f")));
	
		// This test checks that, on re-creation, timestamp changes are noticed
		rgy.disposeIndex(index, "Index test");
		
		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		finder = new SVDBFindByName(index);
		
		List<ISVDBItemBase> items = finder.findItems("class1_2", true);
	
		assertEquals(1, items.size());
		assertEquals("class1_2", SVDBItem.getName(items.get(0)));
		LogFactory.removeLogHandle(log);
	}

	public void disabled_testWSArgFileTimestampUnchanged() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project);
		
		fIndexRebuilt = 0;
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		index.loadIndex(new NullProgressMonitor());
		
		assertEquals("Index not initially rebuilt", 1, fIndexRebuilt);
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index,
				"class1");
		
		// Now, reset the registry
		reinitializeIndexRegistry();
		
		// Sleep to ensure that the timestamp is different
		log.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		log.debug("[NOTE] post-sleep");


		fIndexRebuilt = 0;
		// Now, re-create the index
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		assertEquals("Index rebuilt without cause", 0, fIndexRebuilt);
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index,
				"class1");
	}

	public void disabled_testFSArgFileTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(getName());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project/basic_lib.f");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		
		IndexTestUtils.assertFileHasElements(index, "class1");
		IndexTestUtils.assertDoesNotContain(index, "class1_2");
		
		rgy.close();

		log.debug("** RESET **");
		// Now, reset the registry
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}


		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		log.debug("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/class1_2.svh"));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/basic_lib.f"));

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		
		IndexTestUtils.assertFileHasElements(index, "class1_2");
		
		LogFactory.removeLogHandle(log);
	}


	@Override
	public void index_event(SVDBIndexChangeEvent ev) {
		if (ev.getType() == SVDBIndexChangeEvent.Type.FullRebuild) {
			fIndexRebuilt++;
		}
	}
}
