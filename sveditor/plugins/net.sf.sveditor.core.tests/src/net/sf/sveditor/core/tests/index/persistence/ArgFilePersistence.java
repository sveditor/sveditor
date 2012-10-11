/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.SVPreProcDirectiveScanner;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class ArgFilePersistence extends TestCase 
	implements ISVDBIndexChangeListener {
	
	private File					fTmpDir;
	private int						fIndexRebuilt;
	private IProject				fProject;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();

		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
			fTmpDir = null;
		}
	}
	
	/*
	public void testOVMXbusDirectDumpLoad() throws DBFormatException, DBWriteException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testOVMXbusDirectDumpLoad");
		
		File test_dir = new File(fTmpDir, "testOVMXbusDirectDumpLoad");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		IProject project_dir = TestUtils.createProject("xbus", xbus);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		TestNullIndexCache cache = new TestNullIndexCache();
		
		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, cache, null);
		
		// Force loading
		ISVDBItemIterator item_it = target_index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				errors.add((SVDBMarker)it);
			}
			assertNotNull("Item " + SVDBItem.getName(it) + " has null location");
			if (it instanceof SVDBTask) {
				for (SVDBParamPortDecl p : ((SVDBTask)it).getParams()) {
					assertNotNull("Parameter " + p.getVarList().get(0).getName() + 
							" of " + SVDBItem.getName(it) + " has null location",
							p.getLocation());
				}
			}
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("Unexpected errors: ", 0, errors.size());
		
		SVDBDump dumper = new SVDBDump(SVCorePlugin.getDefault().getVersion());
		
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		dumper.dump(index, out);

		SVDBLoad loader = new SVDBLoad(SVCorePlugin.getDefault().getVersion());
		
		// May throw exception
		loader.load(index, new ByteArrayInputStream(out.toByteArray()));
		
		assertEquals(index.getDumpDBFileList().size(), index.getLoadDBFileList().size());
		
		for (int i=0; i<index.getDumpDBFileList().size(); i++) {
			SVDBFile fd = index.getDumpDBFileList().get(i);
			SVDBFile fl = index.getLoadDBFileList().get(i);
			
			SVDBItemTestComparator c = new SVDBItemTestComparator();
			c.compare(fd, fl);
		}
		TestUtils.deleteProject(project_dir);
		LogFactory.removeLogHandle(log);
		TestCase.fail("Expected fail");
	}
	*/

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

		fProject = TestUtils.createProject("xbus", xbus);

		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));

		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		IndexTestUtils.assertNoErrWarn(log, target_index);

		String path = "${workspace_loc}/xbus/sv/xbus_transfer.sv";
		ISVDBFileSystemProvider fs = ((SVDBArgFileIndex)target_index).getFileSystemProvider();
		SVPreProcessor pp = ((SVDBArgFileIndex)target_index).createPreProcScanner(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		InputStream in = fs.openStream(path);

		log.debug("--> Parse 1");
		SVDBFile file = target_index.parse(new NullProgressMonitor(), in, path, null).second();
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
		SVCorePlugin.getDefault().enableDebug(true);
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

		fProject = TestUtils.createProject(test_proj.getName(), test_proj);

		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));

		ISVDBIndex target_index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ovm_warning_unbalanced_paren/ovm_warning_unbalanced_paren.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		
		String path = "${workspace_loc}/ovm_warning_unbalanced_paren/ovm_warning_unbalanced_paren.svh";
		ISVDBFileSystemProvider fs = ((SVDBArgFileIndex)target_index).getFileSystemProvider();
		SVPreProcessor pp = ((SVDBArgFileIndex)target_index).createPreProcScanner(path);
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		InputStream in = fs.openStream(path);

		log.debug("--> Parse 1");
		SVDBFile file = target_index.parse(new NullProgressMonitor(), in, path, null).second();
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

		IndexTestUtils.assertNoErrWarn(log, target_index);

		LogFactory.removeLogHandle(log);
	}

	public void testWSArgFileTimestampChanged() {
		ByteArrayOutputStream	 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSArgFileTimestampChanged");
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);

		IndexTestUtils.assertNoErrWarn(log, index);

		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		// Sleep to ensure that the timestamp is different
		log.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
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
		TestUtils.copy(out, fProject.getFile(new Path("basic_lib_project/class1_2.svh")));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, fProject.getFile(new Path("basic_lib_project/basic_lib.f")));

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", SVDBItem.getName(target_it));
		LogFactory.removeLogHandle(log);
	}

	public void testWSArgFileTimestampUnchanged() {
		String testname = "testWSArgFileTimestampUnchanged";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		fIndexRebuilt = 0;
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		SVDBClassDecl target_it = null, target_orig = null;
		List<ISVDBItemBase> orig_list = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = (SVDBClassDecl)tmp_it;
				target_orig = (SVDBClassDecl)tmp_it.duplicate();
			}
			orig_list.add(tmp_it.duplicate());
			if (tmp_it.getType() == SVDBItemType.Covergroup) {
				SVDBCovergroup cg = (SVDBCovergroup)tmp_it;
				SVDBCovergroup cg2 = (SVDBCovergroup)cg.duplicate();
				assertEquals(cg, cg2);
			}
		}

		for (int i=0; i<orig_list.size(); i++) {
			if ((orig_list.get(i) instanceof ISVDBScopeItem) &&
					orig_list.get(i).getType() != SVDBItemType.File) {
				assertTrue("Item " + orig_list.get(i).getType() + " " + SVDBItem.getName(orig_list.get(i)) + 
						" Not Equal " + orig_list.get(i).getType() + " " + SVDBItem.getName(orig_list.get(i)),
						orig_list.get(i).equals(orig_list.get(i)));
			}
		}

		assertEquals("Index not initially rebuilt", 1, fIndexRebuilt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
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
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		it = index.getItemIterator(new NullProgressMonitor());
		
		target_it = null;
		List<ISVDBItemBase> new_list = new ArrayList<ISVDBItemBase>();
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			new_list.add(tmp_it);
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = (SVDBClassDecl)tmp_it;
			}
		}
		
		target_it.equals(target_orig);
		
		assertEquals("item count changed", orig_list.size(), new_list.size());
		// Compare individual items first
		for (int i=0; i<orig_list.size(); i++) {
			if (!(orig_list.get(i) instanceof ISVDBScopeItem)) {
				assertTrue("Item " + orig_list.get(i).getType() + " " + SVDBItem.getName(orig_list.get(i)) + 
						" Not Equal " + new_list.get(i).getType() + " " + SVDBItem.getName(new_list.get(i)),
						orig_list.get(i).equals(new_list.get(i)));
			}
		}

		// Compare non-file scopes next
		for (int i=0; i<orig_list.size(); i++) {
			if ((orig_list.get(i) instanceof ISVDBScopeItem) &&
					orig_list.get(i).getType() != SVDBItemType.File &&
					orig_list.get(i).getType() != SVDBItemType.ClassDecl) {
				if (orig_list.get(i).getType() == SVDBItemType.Function &&
						SVDBItem.getName(orig_list.get(i)).equals("new")) {
					SVDBTask f1 = (SVDBTask)orig_list.get(i);
					SVDBTask f2 = (SVDBTask)new_list.get(i);
					f1.equals(f2);
				} else {
					assertTrue("Item " + orig_list.get(i).getType() + " " + SVDBItem.getName(orig_list.get(i)) + 
							" Not Equal " + new_list.get(i).getType() + " " + SVDBItem.getName(new_list.get(i)),
							orig_list.get(i).equals(new_list.get(i)));
				}
			}
		}

		// Compare everything next
		for (int i=0; i<orig_list.size(); i++) {
			if (orig_list.get(i).getType() == SVDBItemType.File &&
					SVDBItem.getName(orig_list.get(i)).equals("class1.svh")) {
				SVDBFile c1 = (SVDBFile)orig_list.get(i);
				SVDBFile c2 = (SVDBFile)new_list.get(i);
				
				c1.equals(c2);
			}
			assertTrue("Item " + orig_list.get(i).getType() + " " + SVDBItem.getName(orig_list.get(i)) + 
					" Not Equal " + new_list.get(i).getType() + " " + SVDBItem.getName(new_list.get(i)),
					orig_list.get(i).equals(new_list.get(i)));
		}

		assertEquals("Index rebuilt without cause", 0, fIndexRebuilt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
	}

	public void testFSArgFileTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSArgFileTimestampChanged");
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(project_dir));
		
		File path = new File(project_dir, "basic_lib_project/basic_lib.f");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		ISVDBItemBase class1_2 = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				class1_2 = tmp_it;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		assertNull("Ensure don't fine class1_2 yet", class1_2);
		
		rgy.save_state();

		log.debug("** RESET **");
		// Now, reset the registry
		rgy.init(TestIndexCacheFactory.instance(project_dir));
		
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
		it = index.getItemIterator(new NullProgressMonitor());
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", SVDBItem.getName(target_it));
		
		LogFactory.removeLogHandle(log);
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fIndexRebuilt++;
	}
	
}
