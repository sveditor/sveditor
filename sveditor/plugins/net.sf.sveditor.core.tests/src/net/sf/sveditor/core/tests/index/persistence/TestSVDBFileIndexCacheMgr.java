package net.sf.sveditor.core.tests.index.persistence;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCache;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;
import net.sf.sveditor.core.tests.SVTestCaseBase;

public class TestSVDBFileIndexCacheMgr extends SVTestCaseBase {
	
	public void testIndexSavedRestored() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		SVDBFileSystem fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		assertFalse(fs.init());
		
		SVDBFileIndexCacheMgr		mgr = new SVDBFileIndexCacheMgr();
		mgr.init(fs);
	
		// Create an index
		mgr.createIndexCache("MY_PROJECT", "BASE_LOCATION");
		
		// Now, close down the manager (which also closes the filesystem)
		mgr.dispose();
		
		fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		assertTrue(fs.init());
		
		mgr = new SVDBFileIndexCacheMgr();
		mgr.init(fs);
		
		// Search for the index we created
		ISVDBIndexCache cache = mgr.findIndexCache("MY_PROJECT", "BASE_LOCATION");
		
		assertNotNull(cache);
	}

	public void testIndexEntriesSavedRestored() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		SVDBFileSystem fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		assertFalse(fs.init());
		
		SVDBFileIndexCacheMgr		mgr = new SVDBFileIndexCacheMgr();
		mgr.init(fs);
	
		// Create an index
		SVDBFileIndexCache cache = mgr.createIndexCache("MY_PROJECT", "BASE_LOCATION");
	
		SVDBFile file = new SVDBFile("mypath");
		SVDBClassDecl cls = new SVDBClassDecl("myclass");
		file.addChildItem(cls);
		
		cache.setFile("/mypath", file, false);
		
		// Now, close down the manager (which also closes the filesystem)
		mgr.dispose();
		
		fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		assertTrue(fs.init());
		
		mgr = new SVDBFileIndexCacheMgr();
		mgr.init(fs);
		
		// Search for the index we created
		cache = mgr.findIndexCache("MY_PROJECT", "BASE_LOCATION");
		assertNotNull(cache);
		
		SVDBFile file2 = cache.getFile(new NullProgressMonitor(), "/mypath");
		assertNotNull(file2);
		
	}
}
