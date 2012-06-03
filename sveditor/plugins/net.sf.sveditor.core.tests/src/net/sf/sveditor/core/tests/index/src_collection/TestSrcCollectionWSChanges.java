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
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSrcCollectionWSChanges extends TestCase 
	implements ISVDBIndexChangeListener {
	
	private int						fIndexRebuilt;
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
			TestUtils.delete(fTmpDir);
			fTmpDir = null;
		}
	}

	public void testFileAdded() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"project", "${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().getItemIterator(new NullProgressMonitor());
		
//		assertEquals("Expecting index to be built once", 1, fIndexRebuilt);
		
		// Create a new class file
		String class_str = 
			"class class_1_2;\n" +
			"    function new();\n" +
			"    endfunction\n" +
			"endclass\n";
		
		IFile class_1_2_file = project_dir.getFile("/project_dir_src_collection_pkg/class_1_2.svh");
		try {
			
			class_1_2_file.create(new StringInputStream(class_str), 
					true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Exception while creating class: " + e.getMessage());
		}

		try {
			index.parse(new NullProgressMonitor(), class_1_2_file.getContents(), 
					"${workspace_loc}" + class_1_2_file.getFullPath(), null);
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		assertEquals("Expecting index to be built twice", 1, fIndexRebuilt);

		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase class_1_2 = null;
		ISVDBItemBase def_function = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class2")) {
				class2 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class3")) {
				class3 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("def_function")) {
				def_function = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
	}

	public void testFileRemoved() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}

		// Create a new class file
		String class_str = 
			"class class_1_2;\n" +
			"    function new();\n" +
			"    endfunction\n" +
			"endclass\n";
		
		IFile class_1_2_file = project_dir.getFile("/project_dir_src_collection_pkg/class_1_2.svh");
		try {
			
			class_1_2_file.create(new StringInputStream(class_str), 
					true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Exception while creating class: " + e.getMessage());
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"project", "${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().getItemIterator(new NullProgressMonitor());
		
		try {
			index.parse(new NullProgressMonitor(), class_1_2_file.getContents(), 
					"${workspace_loc}" + class_1_2_file.getFullPath(), null);
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase class_1_2 = null;
		ISVDBItemBase def_function = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class2")) {
				class2 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class3")) {
				class3 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("def_function")) {
				def_function = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
		
		// Now, remove the file
		try {
			class_1_2_file.delete(true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Failed to delete file: " + e.getMessage());
		}

		// Ask the index to parse the file even though it doesn't exist
		// The goal is to ensure that no exceptions are thrown
		SVDBFile class_1_2_db = null;
		try {
			class_1_2_db = index.parse(new NullProgressMonitor(), 
					new StringInputStream(class_str), 
					"${workspace_loc}" + class_1_2_file.getFullPath(), null);
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		assertEquals("Expecting index to be built twice", 1, fIndexRebuilt);
		assertNull("class_1_2_db is not null", class_1_2_db);


		it = index.getItemIterator(new NullProgressMonitor());
		class1 = null;
		class2 = null;
		class3 = null;
		class_1_2 = null;
		def_function = null;
		markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class2")) {
				class2 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class3")) {
				class3 = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("def_function")) {
				def_function = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));

	}

	// ISVDBIndexChangeListener implementation
	public void index_changed(int reason, SVDBFile file) {
	}

	public void index_rebuilt() {
		fIndexRebuilt++;
	}

}
