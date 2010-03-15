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


package net.sf.sveditor.core.tests.index.src_collection;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class SrcCollectionBasics extends TestCase {
	
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		System.out.println("setUp");
		super.setUp();
		
		SVCorePlugin.getDefault().enableDebug(true);
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		System.out.println("tearDown");
		super.tearDown();

		if (fTmpDir != null) {
			fTmpDir.delete();
			fTmpDir = null;
		}
	}
	
	
	public void testFindSourceRecursePkg() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_pkg/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "project_dir_src_collection_pkg");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		SVDBItem def_function = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			System.out.println("it: " + tmp_it.getType() + " " + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getName().equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", class1.getName());
		
		// rgy.save_state();

	}
	
	public void testFindSourceRecurseNoPkg() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_nopkg/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "project_dir_src_collection_nopkg");
		ISVDBIndex index = rgy.findCreateIndex(
				project_dir.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		SVDBItem def_function = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			System.out.println("it: " + tmp_it.getType() + " " + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getName().equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", class1.getName());
		
		// rgy.save_state();

	}

	public void testBasicClassIncludingModule() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_module_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		SVCorePlugin.getDefault().getProjMgr().init();
		
		File path = new File(project_dir, "basic_module_project");
		ISVDBIndex index = rgy.findCreateIndex(path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", class1.getName());
	}

	public void testBasicClassIncludingInterface() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_interface_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		SVCorePlugin.getDefault().getProjMgr().init();
		
		File path = new File(project_dir, "basic_interface_project");
		ISVDBIndex index = rgy.findCreateIndex(path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", class1.getName());
	}

	public void testBasicClassIncludingProgram() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_program_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		SVCorePlugin.getDefault().getProjMgr().init();
		
		File path = new File(project_dir, "basic_program_project");
		ISVDBIndex index = rgy.findCreateIndex(path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", class1.getName());
	}

}
