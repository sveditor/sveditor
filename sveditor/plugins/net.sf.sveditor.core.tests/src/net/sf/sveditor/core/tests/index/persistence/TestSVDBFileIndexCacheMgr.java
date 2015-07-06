package net.sf.sveditor.core.tests.index.persistence;

import java.io.File;
import java.io.IOException;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSVDBFileIndexCacheMgr extends SVCoreTestCaseBase {
	
	public void testIndexSavedRestored() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		
		ISVDBIndexCacheMgr	mgr = SVCorePlugin.createCacheMgr(fs_dir);
	
		// Create an index
		mgr.createIndexCache("MY_PROJECT", "BASE_LOCATION");
		
		// Now, close down the manager (which also closes the filesystem)
		mgr.dispose();
		
		mgr = SVCorePlugin.createCacheMgr(fs_dir);
		
		// Search for the index we created
		ISVDBIndexCache cache = mgr.findIndexCache("MY_PROJECT", "BASE_LOCATION");
		
		assertNotNull(cache);
		
		mgr.dispose();
	}

	public void testIndexEntriesSavedRestored() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		
		ISVDBIndexCacheMgr		mgr = SVCorePlugin.createCacheMgr(fs_dir);
		assertNotNull(mgr);
	
		// Create an index
		ISVDBIndexCache cache = mgr.createIndexCache("MY_PROJECT", "BASE_LOCATION");
	
		SVDBFile file = new SVDBFile("mypath");
		SVDBClassDecl cls = new SVDBClassDecl("myclass");
		file.addChildItem(cls);
		
		cache.setFile("/mypath", file, false);
		
		// Now, close down the manager (which also closes the filesystem)
		mgr.dispose();
		
		mgr = SVCorePlugin.createCacheMgr(fs_dir);
		
		// Search for the index we created
		cache = mgr.findIndexCache("MY_PROJECT", "BASE_LOCATION");
		assertNotNull(cache);
		
		SVDBFile file2 = cache.getFile(new NullProgressMonitor(), "/mypath");
		assertNotNull(file2);
		
		mgr.dispose();
	}
}
