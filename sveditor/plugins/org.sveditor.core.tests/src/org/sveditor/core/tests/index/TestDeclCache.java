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
package org.sveditor.core.tests.index;

import java.io.File;
import java.util.List;

import org.sveditor.core.tests.IndexTestUtils;
import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

public class TestDeclCache extends SVCoreTestCaseBase {
	
	public void testPackageCacheNonInclude() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject p = TestUtils.createProject("package_cache_non_include", fTmpDir);
		addProject(p);

		utils.copyBundleDirToWS("/data/index/package_cache_non_include", p);
	
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				p.getName(),
				"${workspace_loc}/package_cache_non_include/package_cache_non_include/package_cache_non_include.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
	
		index.init(new NullProgressMonitor(), SVCorePlugin.getDefault().getIndexBuilder());
		index.loadIndex(new NullProgressMonitor());

		List<SVDBDeclCacheItem> pkg_list = index.findGlobalScopeDecl(new NullProgressMonitor(), 
				"package_cache_non_include_pkg", new SVDBFindByNameMatcher());
	
		assertNotNull(pkg_list);
		assertEquals(1, pkg_list.size());
		
		List<SVDBDeclCacheItem> pkg_content = index.findPackageDecl(
				new NullProgressMonitor(), pkg_list.get(0));
		assertNotNull(pkg_content);
		
		SVDBDeclCacheItem cls1=null, cls2=null;
		
		for (SVDBDeclCacheItem item : pkg_content) {
			if (item.getName().equals("cls1")) {
				cls1 = item;
			} else if (item.getName().equals("cls2")) {
				cls2 = item;
			}
		}
		
		assertNotNull(cls1);
		assertNotNull(cls2);
	}

	public void testPackageCacheInclude() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		IProject p = TestUtils.createProject("package_cache_include", fTmpDir);
		addProject(p);

		utils.copyBundleDirToWS("/data/index/package_cache_include", p);
	
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				p.getName(),
				"${workspace_loc}/package_cache_include/package_cache_include/package_cache_include.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
	
		index.init(new NullProgressMonitor(), SVCorePlugin.getDefault().getIndexBuilder());
		index.loadIndex(new NullProgressMonitor());

		List<SVDBDeclCacheItem> pkg_list = index.findGlobalScopeDecl(new NullProgressMonitor(), 
				"package_cache_include_pkg", new SVDBFindByNameMatcher());
	
		assertNotNull(pkg_list);
		assertEquals(1, pkg_list.size());
		assertEquals("package_cache_include_pkg", pkg_list.get(0).getName());
		
		List<SVDBDeclCacheItem> pkg_content = index.findPackageDecl(
				new NullProgressMonitor(), pkg_list.get(0));
		assertNotNull(pkg_content);
		
		SVDBDeclCacheItem cls1=null, cls2=null;
		
		for (SVDBDeclCacheItem item : pkg_content) {
			log.debug("item: " + item.getName());
			if (item.getName().equals("cls1")) {
				cls1 = item;
			} else if (item.getName().equals("cls2")) {
				cls2 = item;
			}
		}
		
		assertNotNull(cls1);
		assertNotNull(cls2);
		
		LogFactory.removeLogHandle(log);
	}

	public void testModuleMembersNotCached() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/index/module_members_not_cached", fTmpDir);
		IProject p = TestUtils.createProject("module_members_not_cached", 
				new File(fTmpDir, "module_members_not_cached"));
		addProject(p);

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				p.getName(),
				"${workspace_loc}/module_members_not_cached/module_members_not_cached.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
	
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"m1", "m2");
		
		IndexTestUtils.assertDoesNotContain(index, 
				"m1_r1", "m1_r2", "m1_r3",
				"m2_r1", "m2_r2", "m2_r3");
	}
}
