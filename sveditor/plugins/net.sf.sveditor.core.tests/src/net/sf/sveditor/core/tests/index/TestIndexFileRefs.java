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
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.refs.SVDBRefCollectorVisitor;
import net.sf.sveditor.core.db.refs.SVDBRefItem;
import net.sf.sveditor.core.db.refs.SVDBRefSearchSpecModIfcRefsByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIndexFileRefs extends SVCoreTestCaseBase {

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
		
		IProject project = TestUtils.createProject("uvm", uvm_src);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv", SVDBLibPathIndexFactory.TYPE, null);
		index.setGlobalDefine("QUESTA", "");
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		for (String filename : index.getFileList(new NullProgressMonitor())) {
			SVDBFileRefCollector finder = new SVDBFileRefCollector();
			SVDBFile file = index.findFile(filename);
			fLog.debug(LEVEL_MIN, "[VISIT FILE] " + filename);
			// MSB: 
//			finder.visitFile(file);
			Map<String, List<Integer>> refs = finder.getReferences();
	
			/*
			for (SVDBRefType t : SVDBRefType.values()) {
				fLog.debug(LEVEL_MIN, "    TYPE: " + t);
				for (String n : ref.getRefSet(t)) {
					fLog.debug(LEVEL_MIN, "        NAME: " + n);
				}
			}
			 */
		}
		
		LogFactory.removeLogHandle(log);
	}

	public void disabled_testUVMComponentRefs() {
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
		
		IProject project = TestUtils.createProject("uvm", uvm_src);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm_pkg.sv", SVDBLibPathIndexFactory.TYPE, null);
		index.setGlobalDefine("QUESTA", "");
		
		long index_build_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long index_build_end = System.currentTimeMillis();
		IndexTestUtils.assertNoErrWarn(log, index);

		long ref_find_start = System.currentTimeMillis();
//MSB:
		List<SVDBRefCacheItem> refs = /* index.findReferences(
				new NullProgressMonitor(), "uvm_component", new SVDBTypeRefMatcher()); */ null;
		
		for (SVDBRefCacheItem item : refs) {
			log.debug("Item: " + item.getFilename());
//			fLog.debug(LEVEL_MIN, "Item: " + item.getFilename());
			List<SVDBRefItem> ref_items = item.findReferences(new NullProgressMonitor());
			for (SVDBRefItem ref_item : ref_items) {
				fLog.debug(LEVEL_MIN, "ref_item: " + ref_item.getLeaf().getType() + " " + 
						SVDBItem.getName(ref_item.getLeaf()) + " in file: " + 
						ref_item.getRoot().getFilePath());
			}
		}
		long ref_find_end = System.currentTimeMillis();
		
		fLog.debug(LEVEL_MIN, "Index-build time: " + (index_build_end-index_build_start));
		fLog.debug(LEVEL_MIN, "Ref-find time: " + (ref_find_end-ref_find_start));
		
		LogFactory.removeLogHandle(log);
	}

	public void testModuleInstRefs() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, getName());
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/wb_ethmac.zip", test_dir);		
		File wb_ethmac = new File(test_dir, "wb_ethmac");
		
		IProject project = TestUtils.createProject("wb_ethmac", wb_ethmac);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/wb_ethmac/wb_ethmac.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
		index.setGlobalDefine("QUESTA", "");
		
		index.loadIndex(new NullProgressMonitor());
		IndexTestUtils.assertNoErrWarn(fLog, index);
		List<SVDBModuleDecl> roots = new ArrayList<SVDBModuleDecl>();
		
		for (SVDBDeclCacheItem module : index.findGlobalScopeDecl(new NullProgressMonitor(), "", 
				new SVDBFindByTypeMatcher(SVDBItemType.ModuleDecl))) {
			fLog.debug(LEVEL_MIN, "module: " + module.getName());
			SVDBRefCollectorVisitor visitor = new SVDBRefCollectorVisitor();
			
			index.findReferences(new NullProgressMonitor(), 
					new SVDBRefSearchSpecModIfcRefsByName(module.getName()), 
					visitor);
			
			if (visitor.getItemList().size() == 0) {
				// Root
				roots.add((SVDBModuleDecl)module.getSVDBItem());
			}
		}

		for (SVDBModuleDecl root : roots) {
			dump_hierarchy(index, root, "");
		}
	}
	
	private void dump_hierarchy(ISVDBIndexIterator index_it, SVDBModuleDecl m, String indent) {
		fLog.debug(LEVEL_MIN, indent + m.getName());
		
		for (ISVDBChildItem it : m.getChildren()) {
			if (it.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInst inst = (SVDBModIfcInst)it;
				List<SVDBDeclCacheItem> mod_it_l = index_it.findGlobalScopeDecl(
						new NullProgressMonitor(), inst.getTypeName(), 
						new SVDBFindByNameMatcher());
				
				
				if (mod_it_l.size() > 0) {
					dump_hierarchy(index_it, 
							(SVDBModuleDecl)mod_it_l.get(0).getSVDBItem(), 
							indent + "    ");
				}
			}
		}
	}
	
}
