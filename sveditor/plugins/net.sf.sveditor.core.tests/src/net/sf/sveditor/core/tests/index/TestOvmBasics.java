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


package net.sf.sveditor.core.tests.index;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestOvmBasics extends SVCoreTestCaseBase {
	
	public void testBasicProcessing() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testBasicProcessing");
		
		SVDBIndexCollection index_mgr = new SVDBIndexCollection("GLOBAL");
		index_mgr.addPluginLibrary(
				fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
						"GLOBAL", "org.ovmworld.ovm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		index_mgr.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index_mgr);
		IndexTestUtils.assertFileHasElements(fLog, index_mgr, 
				"ovm_sequence", "ovm_component");
		index_mgr.dispose();
		LogFactory.removeLogHandle(log);
	}
	
	public void testXbusExample() {
		SVCorePlugin.getDefault().enableDebug(false);
//		SVCorePlugin.getDefault().setDebugLevel(LEVEL_MIN);
		LogHandle log = LogFactory.getLogHandle("testXbusExample");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testXbusExample");
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		IProject p = TestUtils.createProject("xbus", xbus);
		addProject(p);
		
		TestUtils.copy(
				"+define+QUESTA\n" +
				"-f ${workspace_loc}/xbus/examples/compile_questa_sv.f\n",
				p.getFile("sve.f"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/sve.f",
				SVDBArgFileIndexFactory.TYPE, null);		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	public void testTrivialExample() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testTrivialExample");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testTrivialExample");
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File trivial = new File(test_dir, "ovm/examples/trivial");
		
		IProject p = TestUtils.createProject("trivial", trivial);
		addProject(p);
		
		fLog.debug("--> findCreateIndex");
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/trivial/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		fLog.debug("<-- findCreateIndex");
		fLog.debug("--> loadIndex");
		index.loadIndex(new NullProgressMonitor());
		fLog.debug("<-- loadIndex");
		
		/*
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		 */
		
		IndexTestUtils.assertNoErrWarn(log, index);
	
		/*
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		 */
		index.dispose();
		LogFactory.removeLogHandle(log);
	}
	
	public void testSequenceBasicReadWriteExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, "testSequenceBasicReadWriteExample");
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File basic_read_write_sequence = new File(test_dir, "ovm/examples/sequence/basic_read_write_sequence");
		
		IProject p = TestUtils.createProject("basic_read_write_sequence", basic_read_write_sequence);
		addProject(p);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/basic_read_write_sequence/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));

		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "my_driver");
	}

	public void testSequenceSimpleExample() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testSequenceSimpleExample");
		
		File test_dir = new File(fTmpDir, "testSequenceSimpleExample");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File simple = new File(test_dir, "ovm/examples/sequence/simple");
		
		IProject p = TestUtils.createProject("simple", simple);
		addProject(p);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/simple/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "test");

		index.dispose();
		LogFactory.removeLogHandle(log);
	}
	
}
