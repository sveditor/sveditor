/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.index.cache;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.eclipse.hdt.sveditor.core.tests.CoreReleaseTests;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;
import sun.awt.DisplayChangedListener;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBItemIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.eclipse.hdt.sveditor.core.db.persistence.DBFormatException;
import org.eclipse.hdt.sveditor.core.db.persistence.DBWriteException;
import org.eclipse.hdt.sveditor.core.db.persistence.IDBReader;
import org.eclipse.hdt.sveditor.core.db.persistence.IDBWriter;
import org.eclipse.hdt.sveditor.core.db.persistence.SVDBPersistenceRW;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestIndexCache extends SVCoreTestCaseBase {
	
	public void testFileCacheUVMDumpLoadBug() throws IOException, DBFormatException, DBWriteException {
		String testname = "testFileCacheUVMDumpLoadBug";
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File test_dir = new File(fTmpDir, "test");
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();
		LogHandle log = LogFactory.getLogHandle(testname);
		
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File uvm = new File(test_dir, "uvm");
		
		TestUtils.copy(
				"+incdir+.\n" +
				"+define+QUESTA\n" +
				"uvm_pkg.sv\n",
				new File(uvm, "src/uvm.f"));
		
		IProject project = TestUtils.createProject("uvm", uvm);
		addProject(project);

		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
//		SVDBIndexRegistry rgy = new SVDBIndexRegistry();
//		SVCorePlugin.getDefault().setSVDBIndexRegistry(rgy);
//		TestNullIndexCacheFactory test_cache_f = new TestNullIndexCacheFactory();
//		rgy.init(test_cache_f);
		
		long start, end;
		ISVDBIndex index;
		ISVDBItemIterator it;

		// Create the index in-memory
		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/src/uvm.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Iterable<String> l_1 = index.getFileList(new NullProgressMonitor());
		/*SVDBFile f1_1 = */index.findFile(l_1.iterator().next());
		
		end = System.currentTimeMillis();
		log.debug("First Iteration 1: " + (end-start) + "ms");

		/*
		it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		 */
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

	public void testCacheSize() throws IOException, DBFormatException, DBWriteException {
		PrintStream argfile_ps = new PrintStream(
				new File(fTmpDir, "sve.F"));
		
		for (int fileno=1; fileno<=1000; fileno++) {
			PrintStream ps = new PrintStream(
					new File(fTmpDir, "pkg_" + fileno + ".sv"));
			argfile_ps.println("./pkg_" + fileno + ".sv");
			
			ps.println("package pkg_" + fileno + ";");
			for (int classno=1; classno<=10; classno++) {
				ps.println("  class cls_" + fileno + "_" + classno + ";");
				ps.println("  endclass");
			}
			ps.println("endpackage");
			ps.close();
		}
		argfile_ps.close();
		
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();

		for (int i=0; i<4; i++) {
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
				"index_test", new File(fTmpDir, "sve.F").getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);

		long start = System.currentTimeMillis();
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		long end = System.currentTimeMillis();
		System.out.println("Rebuild: " + (end-start));
		
		SVDBFileIndexCache cache = (SVDBFileIndexCache)index.getCache();
		SVDBFileSystem fs = ((SVDBFileIndexCacheMgr)cache.getCacheMgr()).getFileSystem();
		
		System.out.println("Total: " + fs.getNumTotalBlocks() + " Alloc: " + fs.getNumAllocatedBlocks());
		
		fIndexRgy.disposeIndex(index, "Cleanup");
		
		System.out.println("Total: " + fs.getNumTotalBlocks() + " Alloc: " + fs.getNumAllocatedBlocks());
		}
	}
}
