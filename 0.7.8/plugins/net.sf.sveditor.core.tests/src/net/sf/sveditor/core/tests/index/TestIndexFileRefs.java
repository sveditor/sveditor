/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.refs.AbstractSVDBFileRefFinder;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;

public class TestIndexFileRefs extends TestCase {

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
			TestUtils.delete(fTmpDir);
		}
	}

	public void testUVMIncludeRefs() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testXbusExample");
		
		File test_dir = new File(fTmpDir, "testXbusExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File uvm_src = new File(test_dir, "uvm/src");
		
		IProject project_dir = TestUtils.createProject("uvm", uvm_src);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv", SVDBLibPathIndexFactory.TYPE, null);
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		
		for (String filename : index.getFileList(new NullProgressMonitor())) {
			SVDBFileRefCollector finder = new SVDBFileRefCollector();
			SVDBFile file = index.findFile(filename);
			System.out.println("[VISIT FILE] " + filename);
			finder.visitFile(file);
			for (AbstractSVDBFileRefFinder.RefType t : finder.getRefTypeSet()) {
				System.out.println("    TYPE: " + t);
				for (String n : finder.getRefSet(t)) {
					System.out.println("        NAME: " + n);
				}
			}
		}
		
		LogFactory.removeLogHandle(log);
		TestUtils.deleteProject(project_dir);
	}

}
