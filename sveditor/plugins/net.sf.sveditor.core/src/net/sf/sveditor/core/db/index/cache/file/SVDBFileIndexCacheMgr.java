package net.sf.sveditor.core.db.index.cache.file;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgrInt;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;

public class SVDBFileIndexCacheMgr implements ISVDBIndexCacheMgrInt {
	
	private SVDBFileIndexCacheEntry					fCacheHead;
	private SVDBFileIndexCacheEntry					fCacheTail;
	private int										fCacheSize;
	
	private int										fMaxCacheSize = 100;
	
	private boolean									fUseSoftRef = true;
	
	private List<IDBReader>							fPersistenceRdrSet;
	private List<IDBWriter>							fPersistenceWriterSet;

	private List<SVDBFileIndexCache>				fIndexList;

	
	public SVDBFileIndexCacheMgr() {
		fPersistenceRdrSet = new ArrayList<IDBReader>();
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
	}
	
	public ISVDBIndexCache findIndexCache(
			String 			project_name,
			String 			base_location) {
		ISVDBIndexCache ret = null;
		
		synchronized (fIndexList) {
			for (SVDBFileIndexCache c : fIndexList) { 
				if (c.getProjectName().equals(project_name) &&
						c.getBaseLocation().equals(base_location)) {
					ret = c;
					break;
				}
			}
		}
		
		return ret;
	}

	public ISVDBIndexCache createIndexCache(
			String 			project_name,
			String 			base_location) {
		SVDBFileIndexCache ret;

		synchronized (fIndexList) {
			int id = -1;
			for (int i=0; i<fIndexList.size(); i++) {
				if (fIndexList.get(i) == null) {
					id = i;
					break;
				}
			}
			
			if (id == -1) {
				ret = new SVDBFileIndexCache(this, 
						fIndexList.size(), project_name, base_location);
				fIndexList.add(ret);
			} else {
				ret = new SVDBFileIndexCache(this, id,
						project_name, base_location);
				fIndexList.set(id, ret);
			}
		}
		
		return ret;
	}

	public void compactCache(List<ISVDBIndexCache> cache_list) {
		// TODO Auto-generated method stub

	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void sync() {
		// TODO Auto-generated method stub

	}

	/**
	 * Removes a client cache from the manager
	 * @param cache
	 */
	void removeIndexCache(SVDBFileIndexCache cache) {
		synchronized (fIndexList) {
			fIndexList.remove(cache);
		}
		Map<Integer, Map<String, SVDBFileIndexCacheEntry>> c = cache.getCache();
		
		// cache should not be in use, so no need to lock
		synchronized(this) {
			for (Entry<Integer, Map<String, SVDBFileIndexCacheEntry>> ce : c.entrySet()) {
				for (Entry<String, SVDBFileIndexCacheEntry> e : ce.getValue().entrySet()) {
					SVDBFileIndexCacheEntry entry = e.getValue();

					if (entry.getPrev() == null) {
						fCacheHead = entry.getNext();
					} else {
						entry.getPrev().setNext(entry.getNext());
					}

					// If this entry was cached, decrement the cache size
					if (entry.isCached()) {
						fCacheSize--;
					}
				}
			}
		}
	}
	
	/**
	 * Update the state of the cache entry
	 * @param entry
	 */
	synchronized void cacheUpdate(SVDBFileIndexCacheEntry entry) {
		if (entry.isCached()) {
			moveElementToTail(entry);
		} else {
			addElementToTail(entry);
		}
	}

	/**
	 * Note: must always be called from a synchronized context
	 * @param info
	 */
	void addElementToTail(SVDBFileIndexCacheEntry info) {
			// Add references
		info.setCached();
			
			if (fCacheHead == null) {
				// First entry
				fCacheHead = info;
				fCacheTail = info;
				info.setPrev(null);
				info.setNext(null);
			} else {
				// Add the new file info to the linked list
				fCacheTail.setNext(info);
				info.setPrev(fCacheTail);
				fCacheTail = info;
				info.setNext(null);
			}
			fCacheSize++;
			while (fCacheSize > fMaxCacheSize) {
				// Remove a few entries
				removeElement(fCacheHead);
			}
	}
	
	void moveElementToTail(SVDBFileIndexCacheEntry info) {
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
	
	private void removeElement(SVDBFileIndexCacheEntry info) {
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
			
			// Release references
			info.clearCached();
			fCacheSize--;
	}	
	
	private IDBReader allocReader() {
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
	
	private void freeReader(IDBReader reader) {
		synchronized (fPersistenceRdrSet) {
			fPersistenceRdrSet.add(reader);
		}
	}	

	private IDBWriter allocWriter() {
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
	
	private void freeWriter(IDBWriter writer) {
		synchronized (fPersistenceWriterSet) {
			fPersistenceWriterSet.add(writer);
		}
	}	
}
