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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class SrcCollectionPersistence extends SVCoreTestCaseBase implements ISVDBIndexChangeListener {
	
	private IProject				fProject;
	private int						fIndexRebuildCnt;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fProject = null;
	}
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		super.tearDown();
	}

	public void testWSTimestampChanged() {
		ByteArrayOutputStream 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSTimestampChanged");
		
		fIndexRebuildCnt = 0;
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
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

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index not rebuilt", 1, fIndexRebuildCnt);
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", SVDBItem.getName(target_it));
		
		TestUtils.deleteProject(fProject);
		LogFactory.removeLogHandle(log);
	}

	public void testWSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testWSNoChange");
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
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

		log.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		log.debug("[NOTE] post-sleep");

		// Now, reset the registry
		rgy.init(fCacheFactory);

		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), 
				"GENERIC", "${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		index.addChangeListener(this);

		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
		TestUtils.deleteProject(fProject);
		LogFactory.removeLogHandle(log);
	}

	public void testFSTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSTimestampChanged");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
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

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index not rebuilt (target_it=" + target_it + ")", 1, fIndexRebuildCnt);
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", SVDBItem.getName(target_it));

		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	public void testFSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSNoChange");
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
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
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		it = index.getItemIterator(new NullProgressMonitor());
		index.addChangeListener(this);
		
		target_it = null;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", SVDBItem.getName(target_it));
		
		LogFactory.removeLogHandle(log);
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fIndexRebuildCnt++;
	}
	
}
