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


package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.io.InputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SaveMarkersFileSystemProvider;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class TestIndexMissingIncludeDefine extends TestCase {
	
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

	
	public void testWSLibMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index, "${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 2);
	}

	public void testWSArgFileMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc_def/pkg.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index, "${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 2);
	}

	public void testWSSourceCollectionMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project_dir = TestUtils.createProject("ws_sc_project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index, "${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 1);
	}

	public void int_TestMissingIncludeDefine(
			ISVDBIndex					index,
			String						path,
			int							expected_errors) {
		SaveMarkersFileSystemProvider fs_provider_m = new SaveMarkersFileSystemProvider(
					((AbstractSVDBIndex)index).getFileSystemProvider());
		((AbstractSVDBIndex)index).setFileSystemProvider(fs_provider_m);
		
		// Force the file database to be built
		index.getFileDB();
		assertEquals("Expecting a total of two errors", 
				2, fs_provider_m.getMarkers().size());

		// Ensure that the define- and include-missing markers exist
		fs_provider_m.getMarkers().clear();
		// String path = "${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def/basic_lib_pkg.sv"; 
		InputStream in = fs_provider_m.openStream(path);
		SVDBFile file = index.parse(in, path);
		
		assertNotNull("Failed to parse target file", file);
		
		/*
		for (String err : fs_provider_m.getMarkers()) {
			System.out.println("[MARKER] " + err);
		}
		
		assertEquals("Expecting a total of " + expected_errors + " error(s)", 
				expected_errors, fs_provider_m.getMarkers().size());
		 */
	}

}
