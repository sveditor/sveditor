/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.src_collection;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSrcCollectionWSChanges extends SVCoreTestCaseBase 
	implements ISVDBIndexChangeListener {
	
	private int						fIndexRebuilt;

	public void testFileAdded() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"project", "${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().loadIndex(new NullProgressMonitor());
		
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

		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index,
				"class1", "class2", "class3", 
				"class_1_2");
	}

	public void disabled_testFileRemoved() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
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
		
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"project", "${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().loadIndex(new NullProgressMonitor());
		
		try {
			index.parse(new NullProgressMonitor(), class_1_2_file.getContents(), 
					"${workspace_loc}" + class_1_2_file.getFullPath(), null);
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"class1", "class2", "class3", "class_1_2");
		
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
					"${workspace_loc}" + class_1_2_file.getFullPath(), null).second();
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		assertEquals("Expecting index to be built twice", 1, fIndexRebuilt);
		assertNull("class_1_2_db is not null", class_1_2_db);


		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"class1", "class2", "class3");
	}

	// ISVDBIndexChangeListener implementation
	public void index_changed(int reason, SVDBFile file) {
	}

	public void index_rebuilt() {
		fIndexRebuilt++;
	}

}
