package net.sf.sveditor.core.tests.index.cache;

import java.io.File;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.cache.delegating.SVDBSegmentedIndexCache;
import net.sf.sveditor.core.db.index.cache.delegating.SVDBSegmentedIndexCacheMgr;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestSegmentedCache extends SVCoreTestCaseBase {
	
	private SVDBSegmentedIndexCacheMgr			fCacheMgr;
	private File								fCacheDir;
	
	
	
	@Override
	protected void setUp() throws Exception {
		fCacheDir = new File(fTmpDir, "testCacheDir");
		if (fCacheDir.isDirectory()) {
			SVFileUtils.delete(fCacheDir);
		}
		assertTrue(fCacheDir.mkdirs());
		fCacheMgr = new SVDBSegmentedIndexCacheMgr();
		fCacheMgr.init(fCacheDir);

		super.setUp();
	}



	@Override
	protected void tearDown() throws Exception {
		fCacheMgr.dispose();

		super.tearDown();
	}
	
	protected void closeCache() {
		fCacheMgr.dispose();
	}
	
	protected boolean openCache() {
		fCacheMgr = new SVDBSegmentedIndexCacheMgr();
		return fCacheMgr.init(fCacheDir);
	}



	public void testDisposedCacheStorageDeleted() {
		SVDBSegmentedIndexCache cache1 = (SVDBSegmentedIndexCache)
				fCacheMgr.createIndexCache("my_proj", "base_location");
		
		int id;
		
		id = cache1.getCacheId();
		assertTrue(new File(fCacheDir, "" + id).isDirectory());
		
		SVDBSegmentedIndexCache cache2 = (SVDBSegmentedIndexCache)
				fCacheMgr.createIndexCache("my_proj", "base_location");
		id = cache2.getCacheId();
		assertTrue(new File(fCacheDir, "" + id).isDirectory());
	
		cache1.dispose();
		id = cache1.getCacheId();
		assertFalse(new File(fCacheDir, "" + id).isDirectory());
		// Ensure the second cache is still present
		id = cache2.getCacheId();
		assertTrue(new File(fCacheDir, "" + id).isDirectory());
		
		cache2.dispose();
		id = cache2.getCacheId();
		assertFalse(new File(fCacheDir, "" + id).isDirectory());
	}

	public void testReopenOk() {
		SVDBSegmentedIndexCache cache1 = (SVDBSegmentedIndexCache)
				fCacheMgr.createIndexCache("my_proj", "base_location");
		
		int id;
		
		id = cache1.getCacheId();
		assertTrue(new File(fCacheDir, "" + id).isDirectory());
		
		cache1.addFile("/foo/bar", false);
		
		closeCache();
		
		assertTrue(openCache());
		
		Set<String> filelist = cache1.getFileList(false);
		
		assertTrue(filelist.size() == 1);
	}
}
