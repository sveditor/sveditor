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
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestFilesystemLibPersistence extends TestCase {
	
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
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
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "basic_lib_project/basic_lib_pkg.sv");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			System.out.println("tmp_it=" + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(project_dir);
		
		System.out.println("*** SLEEPING");
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
		index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBLibPathIndexFactory.TYPE, null);
		it = index.getItemIterator();
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_1")) {
				target_it = tmp_it;
				break;
			}
		}
		
		System.out.println("target_it=" + target_it);
		
		assertNotNull("located class1_1", target_it);
		assertEquals("class1_1", target_it.getName());
	}

	/**
	 * Tests FileSystemLib persistence by adding a file, saving the database,
	 * and checking whether the changed file list is detected on reload
	 */
	public void testFSLibIndexFilelistChangeDetected() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_missing_inc/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "basic_lib_missing_inc/basic_lib_pkg.sv");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		SVDBMarkerItem missing_inc = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				missing_inc = (SVDBMarkerItem)tmp_it;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		assertNotNull("Assert have missing include marker", missing_inc);
		
		rgy.save_state();

		System.out.println("** RESET **");
		// Now, reset the registry
		rgy.init(project_dir);
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}


		// Change class1.svh
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		System.out.println("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_missing_inc/class1_2.svh"));
		
		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBLibPathIndexFactory.TYPE, null);
		it = index.getItemIterator();
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", target_it.getName());
	}

	
	

}
