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
package net.sf.sveditor.core.tests.index.cache;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.stream.IntStream;

import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.cache.delegating.SVDBSegmentedIndexCache;
import net.sf.sveditor.core.db.index.cache.delegating.SVDBSegmentedIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCache;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheEntry;
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
	
	public void testReferenceAddDelete() {
		SVDBSegmentedIndexCache cache1 = (SVDBSegmentedIndexCache)
				fCacheMgr.createIndexCache("my_proj", "base_location");
	
		Random r = new Random(1000);
		IntStream ri = r.ints();
		Iterator<Integer> ri_it = ri.iterator();
		List<String> filenames = new ArrayList<String>();
		int file_id = 1;
		
		String filename = "/foo/bar";
		cache1.addFile(filename, false);
		SVDBFile file = new SVDBFile(filename);
		filenames.add(filename);
		cache1.setFile(filename, file, false);
		
		for (int i=0; i<1000000; i++) {
			int op = Math.abs(ri_it.next());
			
			switch ((op % 2)) {
			case 0: { // Add a new file
				filename = "/foo/bar_" + file_id;
				file = new SVDBFile(filename);
				file_id++;
				fLog.debug("Add file: " + filename);
				cache1.addFile(filename, false);
				cache1.setFile(filename, file, false);
				filenames.add(filename);
			} break;
			
			case 1: { // Reference a file
				int file_idx = (Math.abs(ri_it.next()) % filenames.size());
				String path = filenames.get(file_idx);
				file = cache1.getFile(new NullProgressMonitor(), path);
				assertNotNull("Failed to find " + path, file);
			} break;
			
			default: {
				TestCase.fail("Unknown operation " + (op%2));
			} break;
			}
		}
		cache1.dispose();
		
		fLog.debug("Added " + filenames.size() + " files");
	}
	
	public void testAddMany() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBSegmentedIndexCache cache1 = (SVDBSegmentedIndexCache)
				fCacheMgr.createIndexCache("my_proj", "base_location");
		
		for (int i=0; i<600000; i++) {
			String filename = "/foo/bar_" + (i+1);
			SVDBFile file = new SVDBFile(filename);
			fLog.debug("Add file: " + filename);
			cache1.addFile(filename, false);
			cache1.setFile(filename, file, false);
		}
		
		cache1.dispose();
	}
	
	public void testMoveAround() {
		SVCorePlugin.getDefault().enableDebug(false);
		List<SVDBFileIndexCacheEntry> all_e = new ArrayList<SVDBFileIndexCacheEntry>();
		
		SVDBSegmentedIndexCacheMgr mgr = new SVDBSegmentedIndexCacheMgr();
		
		assertTrue(mgr.init(fTmpDir));
		
		mgr.test_setMaxCacheSize(4);
	
		for (int i=0; i<4; i++) {
			SVDBFileIndexCacheEntry entry = new SVDBFileIndexCacheEntry(0, "path_" + i, 0);
			mgr.addToCachedList(entry);
			all_e.add(entry);
		}
		
		List<SVDBFileIndexCacheEntry> ent_l;
	
		ent_l = mgr.test_getUnCachedList();
		assertEquals(0, ent_l.size());

		ent_l = mgr.test_getCachedList();
		assertEquals(4, ent_l.size());
		
		checkCacheEntList(ent_l, "path_0", "path_1", "path_2", "path_3");
		
		mgr.ensureUpToDate(ent_l.get(ent_l.size()-1), 0);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_0", "path_1", "path_2", "path_3");
		
		mgr.ensureUpToDate(ent_l.get(0), 0);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_1", "path_2", "path_3", "path_0");
		
		mgr.ensureUpToDate(ent_l.get(1), 0);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_1", "path_3", "path_0", "path_2");
		
		mgr.ensureUpToDate(ent_l.get(ent_l.size()-1), 0);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_1", "path_3", "path_0", "path_2");
		
		SVDBFileIndexCacheEntry entry;
		
		entry = new SVDBFileIndexCacheEntry(0, "path_4", 0);
		mgr.addToCachedList(entry);
		all_e.add(entry);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_3", "path_0", "path_2", "path_4");
		
		entry = new SVDBFileIndexCacheEntry(0, "path_5", 0);
		mgr.addToCachedList(entry);
		all_e.add(entry);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_0", "path_2", "path_4", "path_5");
		
		// Bring back 'path_1'
		mgr.ensureUpToDate(all_e.get(1), 0);
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "path_2", "path_4", "path_5", "path_1");
		
		mgr.dispose();
	}
	
	public void testMultiIndex() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBSegmentedIndexCacheMgr mgr = new SVDBSegmentedIndexCacheMgr();
		
		mgr.test_setMaxCacheSize(4);
		
		SVDBSegmentedIndexCache c1 = mgr.createIndexCache("foo", "base");
		SVDBSegmentedIndexCache c2 = mgr.createIndexCache("foo", "base");
		List<SVDBFileIndexCacheEntry> ent_l;
		
		for (int i=0; i<8; i++) {
			if ((i%2) == 0) {
				String name = "file_1_" + (i/2);
				c1.addFile(name, false);
				c1.setFile(name, new SVDBFile(name), false);
			} else {
				String name = "file_2_" + (i/2);
				c2.addFile(name, false);
				c2.setFile(name, new SVDBFile(name), false);
			}
		}
		
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "file_1_2", "file_2_2", "file_1_3", "file_2_3");
		
		c1.dispose();
		ent_l = mgr.test_getCachedList();
		checkCacheEntList(ent_l, "file_2_2", "file_2_3");
		
//		for (int i=0; i<ent_l.size(); i++) {
//			System.out.println("Ent[" + i + "] " + ent_l.get(i).getPath());
//		}
	}
	
	private void checkCacheEntList(
			List<SVDBFileIndexCacheEntry> 	l, 
			String	...						exp_l) {
		assertEquals(l.size(), exp_l.length);
		
		for (int i=0; i<l.size(); i++) {
			assertEquals(l.get(i).getPath(), exp_l[i]);
		}
	}
}
