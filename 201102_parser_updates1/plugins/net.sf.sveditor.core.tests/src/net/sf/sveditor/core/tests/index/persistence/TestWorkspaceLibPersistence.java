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

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class TestWorkspaceLibPersistence extends TestCase {
	
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
		
		/*
		URL ws = fTmpDir.toURI().toURL();
		Location instanceLoc = Platform.getInstanceLocation();
        instanceLoc.release();
        instanceLoc.set(ws, true);
         */
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
			fTmpDir = null;
		}
	}

	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void testTimestampChangeDetected() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
//			System.out.println("tmp_it=" + SVDBItem.getName(tmp_it));
			
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
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/class1.svh")));
		
		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1_1")) {
				target_it = tmp_it;
				break;
			}
		}
		
		System.out.println("target_it=" + target_it);
		
		assertNotNull("located class1_1", target_it);
		assertEquals("class1_1", SVDBItem.getName(target_it));
	}

	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void testFilelistChangeDetected() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			// System.out.println("tmp_it=" + SVDBItem.getName(tmp_it));
			
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
		System.out.println("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("[NOTE] post-sleep");

		// Change class1.svh
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_missing_inc/class1_2.svh")));
		
		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);
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
	}

}
