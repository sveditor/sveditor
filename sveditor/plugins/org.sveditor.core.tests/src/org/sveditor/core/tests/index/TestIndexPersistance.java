/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.tests.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.sveditor.core.db.index.SVDBIndexChangeEvent;
import org.sveditor.core.db.index.SVDBIndexChangeEvent.Type;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.sveditor.core.log.ILogLevel;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

import org.sveditor.core.tests.CoreReleaseTests;
import org.sveditor.core.tests.IndexTestUtils;
import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

public class TestIndexPersistance extends SVCoreTestCaseBase implements ISVDBIndexChangeListener {
	private int				fRebuildCount;

	
	@Override
	public void index_event(SVDBIndexChangeEvent ev) {
		if (ev.getType() == Type.FullRebuild) {
			try {
				throw new Exception("index_rebuilt");
			} catch (Exception e) {
				fLog.debug("Index Rebuilt", e);
			}
			fRebuildCount++;
		}
	}

	public void disabled_testWSArgFileIndex() {
		SVCorePlugin.getDefault().enableDebug(false);
// 		SVCorePlugin.getDefault().setDebugLevel(0);
		LogHandle log = LogFactory.getLogHandle("testWSArgFileIndex");
		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testArgFileIndex");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File xbus = new File(test_dir, "ovm/examples/xbus");

		IProject p = TestUtils.createProject("xbus", xbus);
		SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
		addProject(p);
		
		ISVDBIndex index;
		SVDBFile   file;
		InputStream in;
		String path = "${workspace_loc}/xbus/examples/xbus_demo_tb.sv";

		log.debug(ILogLevel.LEVEL_MIN, ">==== PASS 1 ====");
		// Create the index
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "xbus",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;
		
		index.loadIndex(new NullProgressMonitor());
		
		in = index.getFileSystemProvider().openStream(path);
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		file = IndexTestUtils.parse(index, in, path, errors).second();
		
		assertNotNull(file);
		assertEquals(1, fRebuildCount);
		
		for (SVDBMarker m : errors) {
			log.debug(ILogLevel.LEVEL_MIN, "[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());

		log.debug(ILogLevel.LEVEL_MIN, "<==== PASS 1 ====");

		// Now, tear down everything
		log.debug(ILogLevel.LEVEL_MIN, ">==== PASS 2 ====");
		reinitializeIndexRegistry();
		
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "xbus",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		fRebuildCount=0;

		in = index.getFileSystemProvider().openStream(path);
		
		Tuple<SVDBFile, SVDBFile> parse_r = index.parse(new NullProgressMonitor(), in, path, null);
		
		assertNotNull(parse_r);
		assertNotNull(parse_r.second());
		
		file = parse_r.second();
		
		assertNotNull(file);
		assertEquals(0, fRebuildCount);
		log.debug(ILogLevel.LEVEL_MIN, "<==== PASS 2 ====");
		
		// Ensure no errors were produced
		assertEquals(0, CoreReleaseTests.getErrors().size());
		LogFactory.removeLogHandle(log);
	}

}
