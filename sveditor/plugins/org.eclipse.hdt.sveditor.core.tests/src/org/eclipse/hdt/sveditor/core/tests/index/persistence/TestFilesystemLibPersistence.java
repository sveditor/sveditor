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

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestFilesystemLibPersistence extends SVCoreTestCaseBase {
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
	}
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
		super.tearDown();
	}
	
	
	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void disabled_testTimestampChangeDetected() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testTimestampChangeDetected");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		assertTrue(project_dir.mkdirs());
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		File path = new File(project_dir, "basic_lib_project/basic_lib.f");
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				path.getAbsolutePath(), SVDBArgFileIndexFactory.TYPE, null);
		
		index.init(new NullProgressMonitor(), null);
		index.loadIndex(new NullProgressMonitor());
	
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), "class1", 
				SVDBFindDefaultNameMatcher.getDefault());
		
		assertEquals(1, result.size());
		
		ISVDBItemBase target_it = result.get(0).getSVDBItem();
		
		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
//		rgy.close();

		// Now, reset the registry
		reinitializeIndexRegistry();
		
		log.debug("*** SLEEPING");
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}


		// Change class1.svh
		ByteArrayOutputStream out = utils.readBundleFile("/data/basic_lib_project/class1.svh");
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_1;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/class1.svh"));
		
		// Now, re-create the index
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.init(new NullProgressMonitor(), null);
		index.loadIndex(new NullProgressMonitor());
		
		result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), "class1_1", 
				SVDBFindDefaultNameMatcher.getDefault());
		
		assertEquals(1, result.size());
		
		target_it = result.get(0).getSVDBItem();
		
		log.debug("target_it=" + target_it);
		
		assertNotNull("located class1_1", target_it);
		assertEquals("class1_1", SVDBItem.getName(target_it));
		
		index.dispose();
		LogFactory.removeLogHandle(log);
	}


}
