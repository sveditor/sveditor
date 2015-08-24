package net.sf.sveditor.core.db.index.cache.delegating;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import com.sun.rmi.rmid.ExecPermission;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgrInt;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheEntry;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataInput;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBDelegatingPersistenceRW;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBSegmentedIndexCacheMgr implements ISVDBIndexCacheMgrInt {
	
	private SVDBFileIndexCacheEntry					fCacheHead;
	private SVDBFileIndexCacheEntry					fCacheTail;
	private int										fCacheSize;
	
	private SVDBFileIndexCacheEntry					fUnCachedHead;
	private SVDBFileIndexCacheEntry					fUnCachedTail;
	
	private int										fMaxCacheSize = 100;
//	private int										fMaxCacheSize = 10;
//	private int										fMaxCacheSize = 1;
	
	private boolean									fUseSoftRef = true;
	
	private List<IDBReader>							fPersistenceRdrSet;
	private List<IDBWriter>							fPersistenceWriterSet;

	private List<SVDBSegmentedIndexCache>			fIndexList;
	private int										fIndexId;

	// File ID for the file containing index data
	private int										fIndexDataId;

	private File									fCacheDir;
	private SVDBFileSystem							fRootFS;
	private LogHandle								fLog;
	private boolean									fDebugEn;
	
	private boolean									fIsDisposed;

	
	public SVDBSegmentedIndexCacheMgr() {
		fPersistenceRdrSet = new ArrayList<IDBReader>();
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCacheMgr");
		fIndexList = new ArrayList<SVDBSegmentedIndexCache>();
	}

	/**
	 * Initialize the cache manager. This is a blocking operation
	 * 
	 * @param fs
	 * @return
	 */
	public synchronized boolean init(File cache_dir) {
		fCacheDir = cache_dir;

		File root_fs = new File(fCacheDir, "root");
	
		if (!root_fs.isDirectory()) {
			root_fs.mkdirs();
		}

		fRootFS = new SVDBFileSystem(root_fs, SVCorePlugin.getVersion());

		boolean full_reinit = false;
		try {
			if (!fRootFS.init()) {
				full_reinit = true;
			}
		} catch (IOException e) {
			full_reinit = true;
		}
		
		if (full_reinit) {
			// TODO: Clean up everything and start over
		}
		
		
		fCacheHead = null;
		fCacheTail = null;
		fCacheSize = 0;
		
		fUnCachedHead = null;
		fUnCachedTail = null;
		
		fIndexList.clear();
		fIndexDataId = -1;
		
		// Attempt to load data from the filesystem
		SVDBFileSystemDataInput user_data = fRootFS.getUserData();
		
		if (user_data != null) {
			try {
				fIndexDataId = user_data.readInt();
				SVDBFileSystemDataInput index_data = fRootFS.readFile("index data", fIndexDataId);
			
				read_state(index_data);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		return true;
	}
	
	private void write_state(SVDBFileSystemDataOutput dat) throws IOException, DBWriteException {
		// Write back the number of indexes
		dat.writeInt(fIndexList.size());
		
		// Now, write back the project/base location details for each index
		for (SVDBSegmentedIndexCache cache : fIndexList) {
			cache.write(dat);
		}
		
		// Now, write back the number of cache entries
		int n_entries = count_entries(fCacheHead) + count_entries(fUnCachedHead);
		int n_cached=0, n_uncached=0;
		
		dat.writeInt(n_entries);
		SVDBFileIndexCacheEntry entry;
		
		entry = fCacheHead;
		while (entry != null) {
			// Ensure entry contents are written back
//			System.out.println("writeBackEntry: " + entry.getPath());
			writeBackEntry(entry);
			
			entry.write(dat);
			entry = entry.getNext();
			n_cached++;
		}
		
		entry = fUnCachedHead;
		while (entry != null) {
			entry.write(dat);
			entry = entry.getNext();
			n_uncached++;
		}
		
//		System.out.println("<-- write_state n_cached=" + n_cached + " n_uncached=" + n_uncached + " " + 
//				(n_cached+n_uncached));
	}
	
	private void read_state(SVDBFileSystemDataInput din) throws IOException {
		fIndexList.clear();
		
		// Read back the number of indexes
		int index_list_size = din.readInt();

		for (int i=0; i<index_list_size; i++) {
			SVDBSegmentedIndexCache cache = SVDBSegmentedIndexCache.read(this, din);
			SVDBFileSystem fs = openFileSystem(cache.getCacheId());
			
			// Initialize with file system
			cache.setFS(fs);
			
			fIndexList.add(cache);
		}
	
		// Read back the cache entries
		int n_entries = din.readInt();
		
		for (int i=0; i<n_entries; i++) {
			SVDBFileIndexCacheEntry entry = SVDBFileIndexCacheEntry.read(din);
			addToUnCachedList(entry);
		}
	}
	
	SVDBFileSystem openFileSystem(int id) {
		
		String fs_dirname = Long.toHexString(id);
		File fs_dir = new File(fCacheDir, fs_dirname);

		if (!fs_dir.isDirectory()) {
			fs_dir.mkdirs();
		}

		SVDBFileSystem fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		try {
			fs.init();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return fs;
	}
	
	private int count_entries(SVDBFileIndexCacheEntry entry) {
		int count = 0;
		
		while (entry != null) {
			count++;
			entry = entry.getNext();
		}
		
		return count;
	}

	public synchronized void sync() {
		
		// TODO: save cache and entry data to the filesystem
		// - TODO: Write-back any dirty cache entries (future)
		// - Construct the filesystem user data:
		//   - List of index caches
	
		SVDBFileSystemDataOutput dat = new SVDBFileSystemDataOutput();
		SVDBFileSystemDataOutput ud = new SVDBFileSystemDataOutput();

		try {
			// Sync the filesystem of each of the active indexes
			for (SVDBSegmentedIndexCache cache : fIndexList) {
				cache.getFS().sync();
			}
			
			if (fIndexDataId != -1) {
				// Delete the file previously used to store index data
				fRootFS.deleteFile("index info", fIndexDataId);
				fIndexDataId = -1;
			}
			
			write_state(dat);
			
			fIndexDataId = fRootFS.writeFile("index info", dat);
			
			// User data is:
			// - Handle to index info
			ud.writeInt(fIndexDataId);
			fRootFS.setUserData(ud);
			
			// Synchronize the filesystem to ensure everything is up-to-date
			fRootFS.sync();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
	}
	
	public synchronized SVDBSegmentedIndexCache findIndexCache(
			String 			project_name,
			String 			base_location) {
		SVDBSegmentedIndexCache ret = null;

		for (SVDBSegmentedIndexCache c : fIndexList) { 
			if (c.getProjectName().equals(project_name) &&
					c.getBaseLocation().equals(base_location)) {
				ret = c;
				break;
			}
		}

		return ret;
	}

	public synchronized SVDBSegmentedIndexCache createIndexCache(
			String 			project_name,
			String 			base_location) {
		SVDBSegmentedIndexCache ret;
		boolean found_id = false;
		
		int id = ((fIndexId+1) & 0xFFFFFF);
		
		while (!found_id) {
			found_id = true;
			
			for (int i=0; i<fIndexList.size(); i++) {
				if (fIndexList.get(i).getCacheId() == id) {
					found_id = false;
					break;
				}
			}
			
			if (!found_id) {
				id = ((id+1) & 0xFFFFFF);
			}
		}

		ret = new SVDBSegmentedIndexCache(this, id, project_name, base_location);
		
		// Create a filesystem for this cache
		SVDBFileSystem fs = openFileSystem(id);
		ret.setFS(fs);
		
		fIndexList.add(ret);
		
		return ret;
	}

	public void compactCache(List<ISVDBIndexCache> cache_list) {
		// TODO Auto-generated method stub

	}

	public synchronized void dispose() {
		// Close down the cache 
		sync();
		
		for (SVDBSegmentedIndexCache cache : fIndexList) {
			try {
				cache.getFS().close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	
		try {
			fRootFS.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		fIndexDataId = -1;
		fIsDisposed = true;
	}

	/**
	 * Remove all entries for this cache
	 * @param cache
	 */
	synchronized void clearIndexCache(SVDBSegmentedIndexCache cache) {
		SVDBFileIndexCacheEntry entry;

		try {
			entry = fCacheHead;
			while (entry != null) {
				if (entry.getCacheId() == cache.getCacheId()) {
					SVDBFileIndexCacheEntry next = entry.getNext();
					deleteEntry(entry);
					entry = next;
				} else {
					entry = entry.getNext();
				}
			}

			entry = fUnCachedHead;
			while (entry != null) {
				if (entry.getCacheId() == cache.getCacheId()) {
					SVDBFileIndexCacheEntry next = entry.getNext();
					deleteEntry(entry);
					entry = next;
				} else {
					entry = entry.getNext();
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private synchronized void deleteEntry(SVDBFileIndexCacheEntry entry) throws IOException {
		if (!entry.onList()) {
			try {
				throw new Exception("Attempting to remove " + entry.getPath() + " that isn't on list");
			} catch (Exception e) {
				e.printStackTrace();
			}
			return;
		}
		if (entry.isCached()) {
			removeFromCachedList(entry);
		} else {
			removeFromUnCachedList(entry);
		}
		entry.clrOnList();
		
		deleteStorage(entry);
	}


	/**
	 * Synchronize cache entries associated with 'cache' to 
	 * the filesystem
	 * 
	 * @param cache
	 */
	public void sync(SVDBSegmentedIndexCache cache) {
	}

	/**
	 * Removes a client cache from the manager
	 * @param cache
	 */
	synchronized void removeIndexCache(SVDBSegmentedIndexCache cache) {
		if (fIsDisposed) {
			return;
		}
		
		// Clear the entries of the cache
		clearIndexCache(cache);
	
		// Remove the cache from the list after clearing entries
		fIndexList.remove(cache);
	}
	
	/**
	 * Ensures that the cache item is up-to-date
	 * 
	 * This method uses the 'mask' parameter, in conjunction with 
	 * the 'loaded' attribute of the entry, to determine which
	 * elements of the entry must be restored from backing store
	 * 
	 * @param entry
	 */
	synchronized void ensureUpToDate(SVDBFileIndexCacheEntry entry, int mask) {
		int loaded_mask;
		
		if (entry.isCached()) {
			moveElementToCachedTail(entry);
			loaded_mask = entry.loadedMask();
		} else {
			removeFromUnCachedList(entry);
			// addToCachedList() ensures index size is observed
			addToCachedList(entry);
			
			loaded_mask = entry.setCached();
			// Need to bring back into the cache
		}
		
		mask ^= loaded_mask;
		
		if ((mask & SVDBFileIndexCacheEntry.BACKED_MASK) != 0) {
			readBackEntry(entry, mask);
		}
	}
	
	/**
	 * Removes the specified entry from the index cache mgr
	 * 
	 * @param entry
	 */
	synchronized void removeEntry(SVDBFileIndexCacheEntry entry) {
		if (entry.isCached()) {
			removeFromCachedList(entry);
		} else {
			removeFromUnCachedList(entry);
		}

		try {
			deleteStorage(entry);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private SVDBSegmentedIndexCache findCache(int id) {
		for (int i=0; i<fIndexList.size(); i++) {
			SVDBSegmentedIndexCache cache = fIndexList.get(i);
			if (cache.getCacheId() == id) {
				return cache;
			}
		}
		return null;
	}

	/**
	 * Deletes storage associated with the specified entry
	 * 
	 * @param entry
	 * @throws IOException
	 */
	private synchronized void deleteStorage(SVDBFileIndexCacheEntry entry) throws IOException {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		if (cache == null) {
			System.out.println("Failed to find cache: " + entry.getCacheId());
			for (int i=0; i<fIndexList.size(); i++) {
				System.out.println("  Cache: " + fIndexList.get(i).getCacheId());
			}
		}
		
		cache.deleteStorage(entry);
	}

	/**
	 * Add a new entry to the uncached list
	 * 
	 * @param entry
	 */
	private synchronized void addToUnCachedList(SVDBFileIndexCacheEntry entry) {
		entry.setOnList();
		if (fUnCachedHead == null) {
			// First entry
			fUnCachedHead = entry;
			fUnCachedTail = entry;
			entry.setPrev(null);
			entry.setNext(null);
		} else {
			// Add the new file info to the linked list
			fUnCachedTail.setNext(entry);
			entry.setPrev(fUnCachedTail);
			fUnCachedTail = entry;
			entry.setNext(null);
		}
	}

	/**
	 * This method is used by a cache to find an entry that was previously
	 * saved and restored but not yet associated with the cache
	 * 
	 * @param cache_id
	 * @param path
	 * @return
	 */
	synchronized SVDBFileIndexCacheEntry findCacheEntry(int cache_id, String path) {
		SVDBFileIndexCacheEntry entry = fCacheHead;
		
		while (entry != null) {
			if (entry.getCacheId() == cache_id && entry.getPath().equals(path)) {
				return entry;
			}
			entry = entry.getNext();
		}
		
		entry = fUnCachedHead;
		
		while (entry != null) {
			if (entry.getCacheId() == cache_id && entry.getPath().equals(path)) {
				return entry;
			}
			entry = entry.getNext();
		}
	
		// Failed to find
		return null;
	}
	
	/**
	 * Load the specified cache from entries held by the cache manager
	 * 
	 * @param cache_id
	 * @param cache
	 */
	synchronized void loadCache(int cache_id, Map<String, SVDBFileIndexCacheEntry> cache) {
		cache.clear();
		
		SVDBFileIndexCacheEntry entry = fCacheHead;
		
		while (entry != null) {
			if (entry.getCacheId() == cache_id) {
				cache.put(entry.getPath(), entry);
			}
			entry = entry.getNext();
		}
		
		entry = fUnCachedHead;
		
		while (entry != null) {
			if (entry.getCacheId() == cache_id) {
				cache.put(entry.getPath(), entry);
			}
			entry = entry.getNext();
		}		
	}

	public synchronized void addToCachedList(SVDBFileIndexCacheEntry entry) {
		entry.setOnList();
		if (fCacheHead == null) {
			// First entry
			fCacheHead = entry;
			fCacheTail = entry;
			entry.setPrev(null);
			entry.setNext(null);
		} else {
			// Add the new file info to the linked list
			fCacheTail.setNext(entry);
			entry.setPrev(fCacheTail);
			fCacheTail = entry;
			entry.setNext(null);
		}
		
		fCacheSize++;
		
		while (fCacheSize > fMaxCacheSize) {
			if (!fCacheHead.isCached()) {
				System.out.println("[ERROR] Head is not cached");
			}
			uncacheEntry(fCacheHead);
		}
	}

	/**
	 * Remove the specified entry from the Uncached list. It is an error
	 * to call this method with entry.isCached() false
	 * 
	 * @param entry
	 */
	synchronized void removeFromUnCachedList(SVDBFileIndexCacheEntry entry) {
		entry.clrOnList();

		if (entry.getPrev() == null) {
			fUnCachedHead = entry.getNext();
		} else {
			entry.getPrev().setNext(entry.getNext());
		}

		if (entry.getNext() == null) {
			fUnCachedTail = entry.getPrev();
		} else {
			entry.getNext().setPrev(entry.getPrev());
		}
		entry.setPrev(null);
		entry.setNext(null);
	}

	synchronized void removeFromCachedList(SVDBFileIndexCacheEntry entry) {
		entry.clrOnList();
		
		// Ensure the entry is not marked cached
		entry.clearCached();
		
		if (entry.getPrev() == null) {
			fCacheHead = entry.getNext();
		} else {
			entry.getPrev().setNext(entry.getNext());
		}

		if (entry.getNext() == null) {
			fCacheTail = entry.getPrev();
		} else {
			entry.getNext().setPrev(entry.getPrev());
		}
		entry.setPrev(null);
		entry.setNext(null);
		fCacheSize--;
	}

	/**
	 * Clear references in the specified entry, such that 
	 * the system can reclaim memory. 
	 * Write data back to the filesystem.
	 * 
	 * @param info
	 */
	synchronized void uncacheEntry(SVDBFileIndexCacheEntry info) {
		// First, 
		if (info.isCached()) {
			// Remove the entry from the cached list, and move
			// to the uncached list
			removeFromCachedList(info);
			
			addToUnCachedList(info);
		
			// Write-back the data
			writeBackEntry(info);
			
			// Release references
			info.clearCached();
		}
	}
	
	synchronized void moveElementToCachedTail(SVDBFileIndexCacheEntry info) {
		if (!info.isCached()) {
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
			return;
		}
		
		if (fCacheHead == null && fCacheTail == null) {
			try {
				throw new Exception("moveElement with none on list: " + info.getPath() + " cached=" + info.isCached());
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		if (fCacheTail != info) {
			if (info.getPrev() == null) {
				fCacheHead = info.getNext();
			} else {
				info.getPrev().setNext(info.getNext());
			}

			if (info.getNext() == null) {
				fCacheTail = info.getPrev();
			} else {
				info.getNext().setPrev(info.getPrev());
			}

			if (fCacheHead == null) {
				// First entry
				fCacheHead = info;
				fCacheTail = info;
				info.setPrev(null);
				info.setNext(null);
			} else {
				// Add the file info to the linked list
				fCacheTail.setNext(info);
				info.setPrev(fCacheTail);
				fCacheTail = info;
				info.setNext(null);
			}
		}
	}
	
	IDBReader allocReader() {
		IDBReader reader = null;
		synchronized (fPersistenceRdrSet) {
			if (fPersistenceRdrSet.size() > 0) {
				reader = fPersistenceRdrSet.remove(fPersistenceRdrSet.size()-1);
			}
		}
		if (reader == null) {
			reader = new SVDBPersistenceRW();
		}
		
		return reader;
	}
	
	void freeReader(IDBReader reader) {
		synchronized (fPersistenceRdrSet) {
			fPersistenceRdrSet.add(reader);
		}
	}	

	IDBWriter allocWriter() {
		IDBWriter writer = null;
		synchronized (fPersistenceWriterSet) {
			if (fPersistenceWriterSet.size() > 0) {
				writer = fPersistenceWriterSet.remove(fPersistenceWriterSet.size()-1);
			}
		}
		if (writer == null) {
			writer = new SVDBPersistenceRW();
		}
		return writer;
	}
	
	void freeWriter(IDBWriter writer) {
		synchronized (fPersistenceWriterSet) {
			fPersistenceWriterSet.add(writer);
		}
	}
	
	private synchronized void writeBackEntry(SVDBFileIndexCacheEntry entry) {
		if (entry.getSVDBFileRef() != null) {
			writeBackSVDBFile(entry);
		}
		
		if (entry.getSVDBPreProcFileRef() != null) {
			writeBackSVDBPreProcFile(entry);
		}
		
		if (entry.getSVDBFileTreeRef() != null) {
			writeBackSVDBFileTree(entry);
		}
		
		if (entry.getMarkersRef() != null) {
			writeBackMarkers(entry);
		}
	}
	
	private synchronized void readBackEntry(SVDBFileIndexCacheEntry entry, int mask) {
		// TODO:
		mask = SVDBFileIndexCacheEntry.ALL_MASK;
		
		if (entry.getSVDBFileId() != -1 && (mask & SVDBFileIndexCacheEntry.SVDB_FILE_MASK) != 0) {
			if (entry.getSVDBFileRef() != null) {
				// Just reset the reference
				entry.setSVDBFileRef(entry.getSVDBFileRef());
			} else {
				readBackSVDBFile(entry);
			}
		}
	
		if (entry.getSVDBPreProcFileId() != -1 && (mask & SVDBFileIndexCacheEntry.SVDB_PREPROC_FILE_MASK) != 0) {
			if (entry.getSVDBPreProcFileRef() != null) {
				// Just reset the reference
				entry.setSVDBPreProcFileRef(entry.getSVDBPreProcFileRef());
			} else {
				readBackSVDBPreProcFile(entry);
			}
		}
		
		if (entry.getSVDBFileTreeId() != -1 && (mask & SVDBFileIndexCacheEntry.SVDB_FILETREE_MASK) != 0) {
			if (entry.getSVDBFileTreeRef() != null) {
				entry.setSVDBFileTreeRef(entry.getSVDBFileTreeRef());
			} else {
				readBackSVDBFileTree(entry);
			}
		}
		
		if (entry.getMarkersId() != -1 && (mask & SVDBFileIndexCacheEntry.MARKERS_MASK) != 0) {
			if (entry.getMarkersRef() != null) {
				entry.setMarkersRef(entry.getMarkersRef());
			} else {
				readBackMarkers(entry);
			}
		}
	}

	private synchronized void writeBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.writeBackSVDBFile(entry);
	}

	private synchronized void readBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.readBackSVDBFile(entry);
	}

	private synchronized void writeBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.writeBackSVDBPreProcFile(entry);
	}
	
	private synchronized void readBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.readBackSVDBPreProcFile(entry);
	}
	
	private synchronized void writeBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.writeBackSVDBFileTree(entry);
	}
	
	private synchronized void readBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.readBackSVDBFileTree(entry);
	}
	
	private synchronized void writeBackMarkers(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.writeBackMarkers(entry);
	}	

	private synchronized void readBackMarkers(SVDBFileIndexCacheEntry entry) {
		SVDBSegmentedIndexCache cache = findCache(entry.getCacheId());
		
		cache.readBackMarkers(entry);
	}
}
