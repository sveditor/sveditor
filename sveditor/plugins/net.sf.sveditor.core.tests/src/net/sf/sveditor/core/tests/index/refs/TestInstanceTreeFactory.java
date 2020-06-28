/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.index.refs;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModuleDecl;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.refs.SVDBInstanceTreeFactory;
import org.eclipse.hdt.sveditor.core.db.refs.SVDBInstanceTreeNode;
import org.eclipse.hdt.sveditor.core.db.refs.SVDBRefCollectorVisitor;
import org.eclipse.hdt.sveditor.core.db.refs.SVDBRefSearchSpecModIfcRefsByName;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByTypeMatcher;

import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestInstanceTreeFactory extends SVCoreTestCaseBase {

	public void testInstTreeFactory_1() {
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
		
		List<SVDBDeclCacheItem> eth_register_l = index.findGlobalScopeDecl(
				new NullProgressMonitor(), "eth_register", 
				new SVDBFindByNameMatcher());
		
		assertEquals(1, eth_register_l.size());
		
		SVDBModuleDecl eth_register = (SVDBModuleDecl)eth_register_l.get(0).getSVDBItem();
		
		SVDBInstanceTreeFactory f = new SVDBInstanceTreeFactory(index);
	
		long start = System.currentTimeMillis();
		SVDBInstanceTreeNode root = f.build(new NullProgressMonitor(), eth_register);
		long end = System.currentTimeMillis();
		fLog.debug("build time: " + (end-start));

		dump_hierarchy("", root);
//		for (SVDBInstanceTreeNode n : root.getInstantiations()) {
//		}
	}

	private void dump_hierarchy(String path, SVDBInstanceTreeNode root) {
		if (root.getInstantiations().size() > 0) {
			for (SVDBInstanceTreeNode n : root.getInstantiations()) {
				dump_hierarchy(path + "." + n.getInstname(), n);
			}
		} else {
			fLog.debug("Path to root: " + path);
		}
	}
}
