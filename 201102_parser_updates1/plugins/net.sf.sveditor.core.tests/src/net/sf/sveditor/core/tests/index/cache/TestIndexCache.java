package net.sf.sveditor.core.tests.index.cache;

import java.io.File;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIndexCache extends TestCase {
	
	public void testFileCacheBasics() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File tmp_dir = TestUtils.createTempDir();
		final File db_dir = new File(tmp_dir, "db");
		File test_dir = new File(tmp_dir, "test");
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testFileCacheBasics");
		
		assertTrue(db_dir.mkdirs());
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);		
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		IProject project_dir = TestUtils.createProject("xbus", xbus);

		SVDBIndexRegistry rgy = new SVDBIndexRegistry();
		SVCorePlugin.getDefault().setSVDBIndexRegistry(rgy);
		ISVDBIndexCacheFactory f = new ISVDBIndexCacheFactory() {
			public ISVDBIndexCache createIndexCache(String project_name,
					String base_location) {
				SVDBDirFS fs = new SVDBDirFS(db_dir);
				ISVDBIndexCache cache = new SVDBFileIndexCache(fs);
				return cache;
			}
		};
		rgy.init(f);
		
		long start, end;
		ISVDBIndex index;
		ISVDBItemIterator it;

		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		List<String> l_1 = index.getFileList(new NullProgressMonitor());
		SVDBFile f1_1 = index.findFile(l_1.get(0));
		
		end = System.currentTimeMillis();
		log.debug("First Iteration 1: " + (end-start) + "ms");

		it = index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			it.nextItem();
		}
		index.dispose();
		end = System.currentTimeMillis();
		
		log.debug("First Iteration 2: " + (end-start) + "ms");

		rgy.init(f);
		start = System.currentTimeMillis();
		index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);

		List<String> l = index.getFileList(new NullProgressMonitor());
		SVDBFile f1 = index.findFile(l.get(0));
		
		end = System.currentTimeMillis();

		log.debug("Second Iteration: " + (end-start) + "ms");

		TestUtils.deleteProject(project_dir);
		LogFactory.removeLogHandle(log);
	}

}
