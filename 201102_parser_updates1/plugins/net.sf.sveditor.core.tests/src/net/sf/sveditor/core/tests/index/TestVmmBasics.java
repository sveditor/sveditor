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
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestVmmBasics extends TestCase {
	
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		/*
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
		 */
	}

	public void testBasicProcessing() {
		SVCorePlugin.getDefault().enableDebug(false);
		File tmpdir = new File(fTmpDir, "no_errors");
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(tmpdir);
	
		SVDBIndexCollectionMgr index_mgr = new SVDBIndexCollectionMgr("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex("GLOBAL", "org.vmmcentral.vmm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		
		ISVDBItemIterator index_it = index_mgr.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		ISVDBItemBase vmm_xtor=null;
		ISVDBItemBase vmm_err=null;
		
		while (index_it.hasNext()) {
			ISVDBItemBase it = index_it.nextItem();
			String name = SVDBItem.getName(it);
			System.out.println("" + it.getType() + " " + name);
			
			if (it.getType() == SVDBItemType.Marker) {
				markers.add((SVDBMarker)it);
			} else if (it.getType() == SVDBItemType.ClassDecl) {
				if (name.equals("vmm_xactor")) {
					vmm_xtor = it;
				}
			} else if (it.getType() == SVDBItemType.MacroDef) {
				if (name.equals("vmm_error")) {
					vmm_err = it;
				}
			} else if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
				
				assertNotNull("Variable " + SVDBItem.getName(v.getParent()) + "." +
						v.getVarList().get(0).getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
		
		assertEquals("Check that no errors were found", 0, markers.size());
		assertNotNull("Check found vmm_error", vmm_err);
		assertNotNull("Check found vmm_xactor", vmm_xtor);
	}
	
	public void testEthernetExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, "testEthernetExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File ethernet = new File(test_dir, "vmm/sv/examples/std_lib/ethernet");
		
		/* IProject project_dir = */ TestUtils.createProject("ethernet", ethernet);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/ethernet/ethernet.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getName().equals(SVDBMarker.MARKER_ERR)) {
					errors.add(m);
				}
			}
			
			System.out.println("tmp_it=" + SVDBItem.getName(tmp_it));
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}

	public void testWishboneExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testWishboneExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File wishbone = new File(test_dir, "vmm/sv/examples/std_lib/wishbone");
		
		/* IProject project_dir = */ TestUtils.createProject("wishbone", wishbone);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/wishbone/wishbone.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getName().equals(SVDBMarker.MARKER_ERR)) {
					errors.add(m);
				}
			}
			
			System.out.println("tmp_it=" + SVDBItem.getName(tmp_it));
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}

	public void testScenariosExample() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testScenariosExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File scenarios = new File(test_dir, "vmm/sv/examples/std_lib/scenarios");

		/* IProject project_dir = */ TestUtils.createProject("scenarios", scenarios);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/scenarios/scenarios.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		SVDBArgFileIndex af_index = (SVDBArgFileIndex)index;
		// ISVDBFileSystemProvider fs_p = af_index.getFileSystemProvider();
		SVPreProcScanner pp = af_index.createPreProcScanner("${workspace_loc}/scenarios/simple_item.sv");
		
		int ch, lineno=1;
		System.out.print(lineno + ": ");
		while ((ch = pp.get_ch()) != -1) {
			System.out.print((char)ch);
			if (ch == '\n') {
				lineno++;
				System.out.print(lineno + ": ");
			}
		}
		
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getName().equals(SVDBMarker.MARKER_ERR)) {
					errors.add(m);
				}
			}
			
//			System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}

}
