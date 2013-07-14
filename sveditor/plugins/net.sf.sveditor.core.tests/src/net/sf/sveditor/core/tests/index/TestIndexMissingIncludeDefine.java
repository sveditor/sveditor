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
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SaveMarkersFileSystemProvider;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIndexMissingIncludeDefine extends SVCoreTestCaseBase {
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
		super.tearDown();
	}

	
	public void testWSLibMissingIncludeDefine() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index, "${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 3);
	}

	public void testWSArgFileMissingIncludeDefine() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
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
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index, "${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 1);
	}

	public void int_TestMissingIncludeDefine(
			ISVDBIndex					index,
			String						path,
			int							expected_errors) {
		LogHandle log = LogFactory.getLogHandle(getName());
		SaveMarkersFileSystemProvider fs_provider_m = new SaveMarkersFileSystemProvider(
					index.getFileSystemProvider());
		index.setFileSystemProvider(fs_provider_m);
		
		// Force the file database to be built
		index.loadIndex(new NullProgressMonitor());
		/*
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		 */
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		for (String file : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> m_tmp = index.getMarkers(file);
			markers.addAll(m_tmp);
			for (SVDBMarker m : m_tmp) {
				log.debug("[MARKER] " + m.getMessage());
			}
		}
	
		/*
		assertEquals("Expecting a total of two errors", 
				2, fs_provider_m.getMarkers().size());
		 */
		assertEquals("Expecting a total of two errors", 2, markers.size());

		// Ensure that the define- and include-missing markers exist
		fs_provider_m.getMarkers().clear();
		// String path = "${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def/basic_lib_pkg.sv"; 
		InputStream in = fs_provider_m.openStream(path);
		List<SVDBMarker> markers_1 = new ArrayList<SVDBMarker>();
		SVDBFile file = index.parse(new NullProgressMonitor(), in, path, markers_1).second();
		
		assertNotNull("Failed to parse target file", file);
		LogFactory.removeLogHandle(log);
	}

}
