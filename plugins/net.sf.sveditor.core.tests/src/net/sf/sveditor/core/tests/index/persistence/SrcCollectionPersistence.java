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
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;

public class SrcCollectionPersistence extends TestCase implements ISVDBIndexChangeListener {
	
	private File					fTmpDir;
	private int						fIndexRebuildCnt;

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

	public void testWSTimestampChanged() {
		ByteArrayOutputStream 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		fIndexRebuildCnt = 0;
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			// System.out.println("tmp_it=" + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(fTmpDir);
		
		// Sleep to ensure that the timestamp is different
		System.out.println("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("[NOTE] post-sleep");

		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/class1_2.svh")));

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator();
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index not rebuilt", 1, fIndexRebuildCnt);
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", target_it.getName());
	}

	public void testWSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;

		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			// System.out.println("tmp_it=" + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());

		rgy.save_state();

		System.out.println("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("[NOTE] post-sleep");

		// Now, reset the registry
		rgy.init(fTmpDir);

		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator();
		index.addChangeListener(this);

		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
	}

	public void testFSTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		SVDBItem class1_2 = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
			} else if (tmp_it.getName().equals("class1_2")) {
				class1_2 = tmp_it;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		assertNull("Ensure don't fine class1_2 yet", class1_2);
		
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
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		System.out.println("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/class1_2.svh"));

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator();
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index not rebuilt (target_it=" + target_it + ")", 1, fIndexRebuildCnt);
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", target_it.getName());
	}

	public void testFSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		SVDBItem class1_2 = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
			} else if (tmp_it.getName().equals("class1_2")) {
				class1_2 = tmp_it;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		assertNull("Ensure don't fine class1_2 yet", class1_2);
		
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
		
		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator();
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fIndexRebuildCnt++;
	}
	
}
