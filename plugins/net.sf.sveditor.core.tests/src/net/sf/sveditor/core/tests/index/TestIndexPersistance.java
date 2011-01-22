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
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestIndexPersistance extends TestCase implements ISVDBIndexChangeListener {
	private File			fTmpDir;
	private int				fRebuildCount;
	
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
		}
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fRebuildCount++;
	}

	public void testWSArgFileIndex() {
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testArgFileIndex");
		File db_dir = new File(fTmpDir, "db");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		if (db_dir.exists()) {
			assertTrue(db_dir.delete());
		}
		assertTrue(db_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		/* IProject project_dir = */ TestUtils.createProject("xbus", xbus);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db_dir);
		
		ISVDBIndex index;
		SVDBFile   file;
		InputStream in;
		String path = "${workspace_loc}/xbus/examples/xbus_demo_tb.sv";

		System.out.println(">==== PASS 1 ====");
		// Create the index
		index = rgy.findCreateIndex("xbus",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;
		
		in = ((SVDBLibIndex)index).getFileSystemProvider().openStream(path); 
		file = index.parse(in, path, new NullProgressMonitor());
		
		assertNotNull(file);
		assertEquals(1, fRebuildCount);
		
		List<SVDBMarkerItem> errors = IndexTests.getErrorsWarnings(index);
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());

		System.out.println("<==== PASS 1 ====");

		// Save the database
		rgy.save_state();

		// Now, tear down everything
		System.out.println(">==== PASS 2 ====");
		rgy.init(db_dir);
		index = rgy.findCreateIndex("xbus",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;

		in = ((SVDBLibIndex)index).getFileSystemProvider().openStream(path); 
		file = index.parse(in, path, new NullProgressMonitor());
		
		assertNotNull(file);
		assertEquals(0, fRebuildCount);
		System.out.println("<==== PASS 2 ====");
		
		// Ensure no errors were produced
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

	public void testWSLibIndex() {
		CoreReleaseTests.clearErrors();
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testLibIndex");
		File db_dir = new File(fTmpDir, "db");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		if (db_dir.exists()) {
			assertTrue(db_dir.delete());
		}
		assertTrue(db_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File ovm = new File(test_dir, "ovm");
		
		/* IProject project_dir = */ TestUtils.createProject("ovm", ovm);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db_dir);
		
		ISVDBIndex index;
		SVDBFile   file;
		InputStream in;
		String path = "${workspace_loc}/ovm/src/base/ovm_component.svh";

		System.out.println(">==== PASS 1 ====");
		// Create the index
		index = rgy.findCreateIndex("ovm",
				"${workspace_loc}/ovm/src/ovm_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;
		
		in = ((SVDBLibIndex)index).getFileSystemProvider().openStream(path); 
		file = index.parse(in, path, new NullProgressMonitor());
		
		assertNotNull(file);
		assertEquals(1, fRebuildCount);
		
		List<SVDBMarkerItem> errors = IndexTests.getErrorsWarnings(index);
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());

		System.out.println("<==== PASS 1 ====");

		// Save the database
		rgy.save_state();

		// Now, tear down everything
		System.out.println(">==== PASS 2 ====");
		rgy.init(db_dir);
		index = rgy.findCreateIndex("ovm",
				"${workspace_loc}/ovm/src/ovm_pkg.sv",
				SVDBLibPathIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;

		in = ((SVDBLibIndex)index).getFileSystemProvider().openStream(path); 
		file = index.parse(in, path, new NullProgressMonitor());
		
		assertNotNull(file);
		assertEquals(0, fRebuildCount);
		System.out.println("<==== PASS 2 ====");
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}

}
