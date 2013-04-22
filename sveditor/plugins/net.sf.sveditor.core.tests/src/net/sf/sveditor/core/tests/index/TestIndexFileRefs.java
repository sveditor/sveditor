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
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.db.refs.SVDBRefCacheEntry;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.refs.SVDBRefItem;
import net.sf.sveditor.core.db.refs.SVDBRefType;
import net.sf.sveditor.core.db.refs.SVDBTypeRefMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIndexFileRefs extends SVCoreTestCaseBase {

	private IProject		fProject;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
	
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		super.tearDown();
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
		
		fProject = TestUtils.createProject("uvm", uvm_src);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv", SVDBLibPathIndexFactory.TYPE, null);
		index.setGlobalDefine("QUESTA", "");
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		for (String filename : index.getFileList(new NullProgressMonitor())) {
			SVDBFileRefCollector finder = new SVDBFileRefCollector();
			SVDBFile file = index.findFile(filename);
			System.out.println("[VISIT FILE] " + filename);
			finder.visitFile(file);
			SVDBRefCacheEntry ref = finder.getReferences();
		
			for (SVDBRefType t : SVDBRefType.values()) {
				System.out.println("    TYPE: " + t);
				for (String n : ref.getRefSet(t)) {
					System.out.println("        NAME: " + n);
				}
			}
		}
		
		LogFactory.removeLogHandle(log);
	}

	public void testUVMComponentRefs() {
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
		
		fProject = TestUtils.createProject("uvm", uvm_src);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv", SVDBLibPathIndexFactory.TYPE, null);
		index.setGlobalDefine("QUESTA", "");
		
		long index_build_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long index_build_end = System.currentTimeMillis();
		IndexTestUtils.assertNoErrWarn(log, index);

		long ref_find_start = System.currentTimeMillis();
		List<SVDBRefCacheItem> refs = index.findReferences(
				new NullProgressMonitor(), "uvm_component", new SVDBTypeRefMatcher());
		
		for (SVDBRefCacheItem item : refs) {
			log.debug("Item: " + item.getFilename());
//			System.out.println("Item: " + item.getFilename());
			List<SVDBRefItem> ref_items = item.findReferences(new NullProgressMonitor());
			for (SVDBRefItem ref_item : ref_items) {
				System.out.println("ref_item: " + ref_item.getLeaf().getType() + " " + 
						SVDBItem.getName(ref_item.getLeaf()) + " in file: " + 
						ref_item.getRoot().getFilePath());
			}
		}
		long ref_find_end = System.currentTimeMillis();
		
		System.out.println("Index-build time: " + (index_build_end-index_build_start));
		System.out.println("Ref-find time: " + (ref_find_end-ref_find_start));
		
		LogFactory.removeLogHandle(log);
	}
	
}
