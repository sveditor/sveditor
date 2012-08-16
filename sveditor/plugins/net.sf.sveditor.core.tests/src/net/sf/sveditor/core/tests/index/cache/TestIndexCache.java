/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.cache;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIndexCache extends TestCase {
	
	private File			fTmpDir;
	private IProject		fProject;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getJobMgr().dispose();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testFileCacheBasics() {
		String testname = "testFileCacheBasics";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File test_dir = new File(fTmpDir, "test");
		final File db_dir = new File(fTmpDir, "db");
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		CoreReleaseTests.clearErrors();
		
		assertTrue(db_dir.mkdirs());
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", fTmpDir);		
		File xbus = new File(fTmpDir, "ovm/examples/xbus");
		
		fProject = TestUtils.createProject("xbus", xbus);

		SVDBIndexRegistry rgy = new SVDBIndexRegistry();
		SVCorePlugin.getDefault().setSVDBIndexRegistry(rgy);
		ISVDBIndexCacheFactory f = new ISVDBIndexCacheFactory() {
			public ISVDBIndexCache createIndexCache(String project_name,
					String base_location) {
				SVDBDirFS fs = new SVDBDirFS(db_dir);
				fs.setEnableAsyncClear(false);
				ISVDBIndexCache cache = new SVDBFileIndexCache(fs);
				return cache;
			}

			public void compactCache(List<ISVDBIndexCache> cache_list) {}
		};
		rgy.init(f);
		
		long start, end;
		ISVDBIndex index;
		ISVDBItemIterator it;

		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Set<String> l_1 = index.getFileList(new NullProgressMonitor());
		/* SVDBFile f1_1 = */index.findFile(l_1.iterator().next());
		
		end = System.currentTimeMillis();
		log.debug("First Iteration 1: " + (end-start) + "ms");

		it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		index.dispose();
		end = System.currentTimeMillis();
		
		log.debug("First Iteration 2: " + (end-start) + "ms");

		rgy.init(f);
		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Set<String> l = index.getFileList(new NullProgressMonitor());
		for (String file : l) {
			/*SVDBFile f1 = */index.findFile(file);
		}
		
		end = System.currentTimeMillis();

		log.debug("Second Iteration: " + (end-start) + "ms");

		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testFileCacheBasicsUVM() {
		String testname = "testFileCacheBasicsUVM";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		final File db_dir = new File(fTmpDir, "db");
		File test_dir = new File(fTmpDir, "test");
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();
		LogHandle log = LogFactory.getLogHandle(testname);
		
		assertTrue(db_dir.mkdirs());
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File uvm = new File(test_dir, "uvm");
		
		fProject = TestUtils.createProject("uvm", uvm);

		SVDBIndexRegistry rgy = new SVDBIndexRegistry();
		SVCorePlugin.getDefault().setSVDBIndexRegistry(rgy);
		ISVDBIndexCacheFactory f = new ISVDBIndexCacheFactory() {
			public ISVDBIndexCache createIndexCache(String project_name,
					String base_location) {
				SVDBDirFS fs = new SVDBDirFS(db_dir);
				fs.setEnableAsyncClear(false);
				ISVDBIndexCache cache = new SVDBFileIndexCache(fs);
				return cache;
			}

			public void compactCache(List<ISVDBIndexCache> cache_list) {}
		};
		rgy.init(f);
		
		long start, end;
		ISVDBIndex index;
		ISVDBItemIterator it;

		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/src/uvm_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);

		Set<String> l_1 = index.getFileList(new NullProgressMonitor());
		/* SVDBFile f1_1 = */index.findFile(l_1.iterator().next());
		
		end = System.currentTimeMillis();
		log.debug("First Iteration 1: " + (end-start) + "ms");

		it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		index.dispose();
		end = System.currentTimeMillis();
		
		log.debug("First Iteration 2: " + (end-start) + "ms");

		rgy.init(f);
		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);

		/*
		Set<String> l = index.getFileList(new NullProgressMonitor());
		for (String file : l) {
			System.out.println("--> findFile: " + file);
			System.out.flush();
			SVDBFile f1 = index.findFile(file);
			System.out.println("<-- findFile: " + file);
			System.out.flush();
		}
		 */
		/*SVDBFile file = */ 
				index.findFile("${workspace_loc}/uvm/src/base/uvm_resource_specializations.svh");
		
		
		
		end = System.currentTimeMillis();

		log.debug("Second Iteration: " + (end-start) + "ms");

		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

	public void testFileCacheUVMDumpLoadBug() throws IOException, DBFormatException, DBWriteException {
		String testname = "testFileCacheUVMDumpLoadBug";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		final File db_dir = new File(fTmpDir, "db");
		File test_dir = new File(fTmpDir, "test");
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();
		LogHandle log = LogFactory.getLogHandle(testname);
		
		
		assertTrue(db_dir.mkdirs());
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File uvm = new File(test_dir, "uvm");
		
		fProject = TestUtils.createProject("uvm", uvm);

		SVDBIndexRegistry rgy = new SVDBIndexRegistry();
		SVCorePlugin.getDefault().setSVDBIndexRegistry(rgy);
		TestNullIndexCacheFactory test_cache_f = new TestNullIndexCacheFactory();
		rgy.init(test_cache_f);
		
		long start, end;
		ISVDBIndex index;
		ISVDBItemIterator it;

		// Create the index in-memory
		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/src/uvm_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);

		Set<String> l_1 = index.getFileList(new NullProgressMonitor());
		/*SVDBFile f1_1 = */index.findFile(l_1.iterator().next());
		
		end = System.currentTimeMillis();
		log.debug("First Iteration 1: " + (end-start) + "ms");

		it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		index.dispose();
		end = System.currentTimeMillis();
		
		log.debug("First Iteration 2: " + (end-start) + "ms");

		SVDBFile file = 
				index.findFile("${workspace_loc}/uvm/src/base/uvm_resource_specializations.svh");

		SVCorePlugin.getDefault().enableDebug(false);

		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutputStream dos = new DataOutputStream(bos);
		IDBWriter writer = null;
		try {
			writer = new SVDBPersistenceRW();
		} catch (Exception e) {
			e.printStackTrace();
		}
		writer.setDebugEn(true);
		IDBReader reader = new SVDBPersistenceRW();
		reader.setDebugEn(true);
		
		writer.init(dos);
		writer.writeObject(file.getClass(), file);
		
		dos.flush();
		bos.flush();
		
		ByteArrayInputStream bis = new ByteArrayInputStream(bos.toByteArray());
		DataInputStream din = new DataInputStream(bis);
		reader.init(din);
		
		SVDBFile file_2 = new SVDBFile();
		reader.readObject(null, file_2.getClass(), file_2);
		
		end = System.currentTimeMillis();

		log.debug("Second Iteration: " + (end-start) + "ms");

		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

}
