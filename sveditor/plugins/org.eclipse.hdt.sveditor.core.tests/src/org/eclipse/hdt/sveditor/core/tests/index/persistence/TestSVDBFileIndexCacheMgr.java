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
package org.eclipse.hdt.sveditor.core.tests.index.persistence;

import java.io.File;
import java.io.IOException;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;

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
