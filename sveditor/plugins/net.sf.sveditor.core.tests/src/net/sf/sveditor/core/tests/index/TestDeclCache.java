package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.old.SVDBArgFileIndex;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;

public class TestDeclCache extends TestCase {
	private IProject			fProject;
	private File				fTmpDir;
	
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
			fProject = null;
		}
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testPackageCacheNonInclude() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		fProject = TestUtils.createProject("package_cache_non_include", fTmpDir);

		utils.copyBundleDirToWS("/data/index/package_cache_non_include", fProject);
	
		ISVDBIndex index = new SVDBArgFileIndex("project", 
				"${workspace_loc}/package_cache_non_include/package_cache_non_include/package_cache_non_include.f",
				new SVDBWSFileSystemProvider(),
				new InMemoryIndexCache(),
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
		String testname = "testPackageCacheInclude";
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		fProject = TestUtils.createProject("package_cache_include", fTmpDir);

		utils.copyBundleDirToWS("/data/index/package_cache_include", fProject);
	
		ISVDBIndex index = new SVDBArgFileIndex("project", 
				"${workspace_loc}/package_cache_include/package_cache_include/package_cache_include.f",
				new SVDBWSFileSystemProvider(),
				new InMemoryIndexCache(),
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
	
}
