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
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.SVPreProcDirectiveScanner;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestVmmBasics extends TestCase {
	
	private IProject		fProject;
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testBasicProcessing() {
		LogHandle log = LogFactory.getLogHandle("testBasicProcessing");
		SVCorePlugin.getDefault().enableDebug(false);
		File tmpdir = new File(fTmpDir, "no_errors");
		
		if (tmpdir.exists()) {
			TestUtils.delete(tmpdir);
		}
		assertTrue(tmpdir.mkdirs());
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(tmpdir));
	
		SVDBIndexCollection index_mgr = new SVDBIndexCollection("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex(new NullProgressMonitor(), "GLOBAL", "org.vmmcentral.vmm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		
		ISVDBItemIterator index_it = index_mgr.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		ISVDBItemBase vmm_xtor=null;
		
		while (index_it.hasNext()) {
			ISVDBItemBase it = index_it.nextItem();
			String name = SVDBItem.getName(it);
			log.debug("" + it.getType() + " " + name);
			
			if (it.getType() == SVDBItemType.Marker) {
				markers.add((SVDBMarker)it);
			} else if (it.getType() == SVDBItemType.ClassDecl) {
				if (name.equals("vmm_xactor")) {
					vmm_xtor = it;
				}
			} else if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
				
				SVDBVarDeclItem vi = (SVDBVarDeclItem)v.getChildren().iterator().next();
				assertNotNull("Variable " + SVDBItem.getName(v.getParent()) + "." +
						vi.getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
		
		assertEquals("Check that no errors were found", 0, markers.size());
		assertNotNull("Check found vmm_xactor", vmm_xtor);
		LogFactory.removeLogHandle(log);
	}
	
	public void testEthernetExample() {
		LogHandle log = LogFactory.getLogHandle("testEthernetExample");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, "testEthernetExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File ethernet = new File(test_dir, "vmm/sv/examples/std_lib/ethernet");
		
		fProject = TestUtils.createProject("ethernet", ethernet);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/ethernet/ethernet.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			log.debug("tmp_it=" + SVDBItem.getName(tmp_it));
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		LogFactory.removeLogHandle(log);
	}

	public void testWishboneExample() {
		LogHandle log = LogFactory.getLogHandle("testWishboneExample");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testWishboneExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File wishbone = new File(test_dir, "vmm/sv/examples/std_lib/wishbone");
		
		fProject = TestUtils.createProject("wishbone", wishbone);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), 
				"GENERIC", "${workspace_loc}/wishbone/wishbone.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			log.debug("tmp_it=" + SVDBItem.getName(tmp_it));
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		LogFactory.removeLogHandle(log);
	}

	public void testScenariosExample() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testScenariosExample");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testScenariosExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.copyBundleDirToFS("/vmm/", test_dir);
		File scenarios = new File(test_dir, "vmm/sv/examples/std_lib/scenarios");

		fProject = TestUtils.createProject("scenarios", scenarios);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/scenarios/scenarios.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		SVDBArgFileIndex af_index = (SVDBArgFileIndex)index;
		// ISVDBFileSystemProvider fs_p = af_index.getFileSystemProvider();
		SVPreProcessor pp = af_index.createPreProcScanner("${workspace_loc}/scenarios/simple_sequencer.sv");
	
		SVPreProcOutput pp_out = pp.preprocess();
		
		int ch, lineno=1;
		StringBuilder sb_dbg = new StringBuilder();
		sb_dbg.append(lineno + ": ");
		StringBuilder sb = new StringBuilder();
		while ((ch = pp_out.get_ch()) != -1) {
			sb_dbg.append((char)ch);
			sb.append((char)ch);
			if (ch == '\n') {
				lineno++;
				sb_dbg.append(lineno + ": ");
			}
		}
		log.debug("Content\n" + sb_dbg.toString());
		
		SVDBTestUtils.parse(log, sb.toString(), "preProcessed.simple_sequencer.sv", false);
		
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
//			log.debug("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		LogFactory.removeLogHandle(log);
	}

}
