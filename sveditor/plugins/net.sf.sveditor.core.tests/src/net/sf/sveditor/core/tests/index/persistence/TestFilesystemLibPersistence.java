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
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestFilesystemLibPersistence extends SVCoreTestCaseBase {
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
	}
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		
		super.tearDown();
	}
	
	
	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void testTimestampChangeDetected() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testTimestampChangeDetected");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			TestUtils.delete(project_dir);
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project/basic_lib_pkg.sv");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				path.getAbsolutePath(), SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			log.debug("tmp_it=" + SVDBItem.getName(tmp_it));
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(fCacheFactory);
		
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
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
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
		
		log.debug("target_it=" + target_it);
		
		assertNotNull("located class1_1", target_it);
		assertEquals("class1_1", SVDBItem.getName(target_it));
		
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Tests FileSystemLib persistence by adding a file, saving the database,
	 * and checking whether the changed file list is detected on reload
	 */
	public void testFSLibIndexFilelistChangeDetected() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSLibIndexFilelistChangeDetected");
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_missing_inc/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_missing_inc/basic_lib_pkg.sv");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				path.getAbsolutePath(), SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase target_it = null;
		SVDBMarker missing_inc = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				missing_inc = (SVDBMarker)tmp_it;
			}
		}
		
		for (String file : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> markers = index.getMarkers(file);
			for (SVDBMarker m : markers) {
				missing_inc = m;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		assertNotNull("Assert have missing include marker", missing_inc);
		
		rgy.save_state();

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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		log.debug("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_missing_inc/class1_2.svh"));
		
		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				path.getAbsolutePath(), SVDBLibPathIndexFactory.TYPE, null);
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
		index.dispose();
	}

	
	

}
