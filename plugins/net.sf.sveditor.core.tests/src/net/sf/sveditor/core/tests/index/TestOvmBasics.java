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
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestOvmBasics extends TestCase {
	
	private File			fTmpDir;
	
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

	public void testBasicProcessing() {
		File tmpdir = new File(fTmpDir, "no_errors");
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(tmpdir);
	
		SVDBIndexCollectionMgr index_mgr = new SVDBIndexCollectionMgr("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex("GLOBAL", "org.ovmworld.ovm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		
		ISVDBItemIterator<SVDBItem> index_it = index_mgr.getItemIterator();
		List<SVDBMarkerItem> markers = new ArrayList<SVDBMarkerItem>();
		SVDBItem ovm_component=null;
		SVDBItem ovm_sequence=null;
		
		while (index_it.hasNext()) {
			SVDBItem it = index_it.nextItem();
			System.out.println("" + it.getType() + " " + it.getName());
			
			if (it.getType() == SVDBItemType.Marker) {
				markers.add((SVDBMarkerItem)it);
			} else if (it.getType() == SVDBItemType.Class) {
				if (it.getName().equals("ovm_component")) {
					ovm_component = it;
				} else if (it.getName().equals("ovm_sequence")) {
					ovm_sequence = it;
				}
			} else if (it.getType() == SVDBItemType.Macro) {
			} else if (it.getType() == SVDBItemType.VarDecl) {
				SVDBVarDeclItem v = (SVDBVarDeclItem)it;
				
				assertNotNull("Variable " + it.getParent().getName() + "." +
						it.getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
		
		for (SVDBMarkerItem m : markers) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		
		assertEquals("Check that no errors were found", 0, markers.size());
		assertNotNull("Check found ovm_sequence", ovm_sequence);
		assertNotNull("Check found ovm_component", ovm_component);
	}
	
	public void testXbusExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testXbusExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/ovm/", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		/* IProject project_dir = */ TestUtils.createProject("xbus", xbus);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)tmp_it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}

	public void testTrivialExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testTrivialExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/ovm/", test_dir);
		File trivial = new File(test_dir, "ovm/examples/trivial");
		
		/* IProject project_dir = */ TestUtils.createProject("trivial", trivial);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/trivial/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)tmp_it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}
	
	public void testSequenceBasicReadWriteExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testSequenceBasicReadWriteExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/ovm/", test_dir);
		File basic_read_write_sequence = new File(test_dir, "ovm/examples/sequence/basic_read_write_sequence");
		
		/* IProject project_dir = */ TestUtils.createProject("basic_read_write_sequence", basic_read_write_sequence);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/basic_read_write_sequence/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		SVDBModIfcClassDecl my_driver = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)tmp_it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			} else if (tmp_it.getType() == SVDBItemType.Class &&
					tmp_it.getName().equals("my_driver")) {
				my_driver = (SVDBModIfcClassDecl)tmp_it;
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		
		assertNotNull(my_driver);
	}

	public void testSequenceSimpleExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testSequenceSimpleExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/ovm/", test_dir);
		File simple = new File(test_dir, "ovm/examples/sequence/simple");
		
		/* IProject project_dir = */ TestUtils.createProject("simple", simple);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/simple/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		SVDBModIfcClassDecl simple_driver = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)tmp_it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			} else if (tmp_it.getType() == SVDBItemType.Class &&
					tmp_it.getName().equals("simple_driver")) {
				simple_driver = (SVDBModIfcClassDecl)tmp_it;
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		
		assertNotNull(simple_driver);
	}


}
