package net.sf.sveditor.core.db.index.cache.file;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgrInt;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFileIndexCacheMgr implements ISVDBIndexCacheMgrInt {
	
	private SVDBFileIndexCacheEntry					fCacheHead;
	private SVDBFileIndexCacheEntry					fCacheTail;
	private int										fCacheSize;
	
	private SVDBFileIndexCacheEntry					fUnCachedHead;
	private SVDBFileIndexCacheEntry					fUnCachedTail;
	
	private int										fMaxCacheSize = 100;
	
	private boolean									fUseSoftRef = true;
	
	private List<IDBReader>							fPersistenceRdrSet;
	private List<IDBWriter>							fPersistenceWriterSet;

	private List<SVDBFileIndexCache>				fIndexList;
	
	private SVDBFileSystem							fFileSystem;
	private LogHandle								fLog;
	private boolean									fDebugEn;

	
	public SVDBFileIndexCacheMgr() {
		fPersistenceRdrSet = new ArrayList<IDBReader>();
		fPersistenceWriterSet = new ArrayList<IDBWriter>();
		fLog = LogFactory.getLogHandle("SVDBFileIndexCacheMgr");
		fIndexList = new ArrayList<SVDBFileIndexCache>();
	}
	
	public boolean init(SVDBFileSystem fs) {
		fFileSystem = fs;

		return false;
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
		// TODO: save cache and entry data to the filesystem

	}

	/**
	 * Removes a client cache from the manager
	 * @param cache
	 */
	void removeIndexCache(SVDBFileIndexCache cache) {
		synchronized (fIndexList) {
			fIndexList.remove(cache);
		}
		Map<String, SVDBFileIndexCacheEntry> c = cache.getCache();
		
		// cache should not be in use, so no need to lock
		synchronized(this) {
			for (SVDBFileIndexCacheEntry entry : c.values()) {
				
				if (entry.isCached()) {
					// Remove from the cached list
					if (entry.getPrev() == null) {
						fCacheHead = entry.getNext();
					} else {
						entry.getPrev().setNext(entry.getNext());
					}					
					fCacheSize--;
				} else {
					if (entry.getPrev() == null) {
						fUnCachedHead = entry.getNext();
					} else {
						entry.getPrev().setNext(entry.getNext());
					}					
				}
			}			
		}
	}
	
	/**
	 * Ensures that the cache item is up-to-date
	 * @param entry
	 */
	synchronized void ensureUpToDate(SVDBFileIndexCacheEntry entry) {
		if (entry.isCached()) {
			moveElementToCachedTail(entry);
		} else {
			// Need to bring back into the cache
			readBackEntry(entry);
			
			removeFromUnCachedList(entry);
			
			entry.setCached();
		
			// addToCachedList() ensures index size is observed
			addToCachedList(entry);
		}
	}

	/**
	 * Add a new entry to the uncached list
	 * 
	 * @param entry
	 */
	public synchronized void addToUnCachedList(SVDBFileIndexCacheEntry entry) {
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

	public synchronized void addToCachedList(SVDBFileIndexCacheEntry entry) {
		System.out.println("addToCachedList: " + entry.getPath() + " entries=" + fCacheSize);
		
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
			System.out.println("Uncache entry: " + fCacheHead.getPath());
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
	}

	synchronized void removeFromCachedList(SVDBFileIndexCacheEntry entry) {
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
	}
	
	/**
	 * Note: must always be called from a synchronized context
	 * @param info
	void addElementToTail(SVDBFileIndexCacheEntry info) {

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
		
		if (info.isCached()) {
			
		} else {
			// Add references
			
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
				System.out.println("uncacheEntry: " + fCacheHead);
				// Free a few cached entries
				// TODO: this needs more thought
				uncacheEntry(fCacheHead);
			}
		}
		info.setCached();
	}
	 */

	/**
	 * Clear references in the specified entry, such that 
	 * the system can reclaim memory. 
	 * Write data back to the filesystem.
	 * 
	 * @param info
	 */
	void uncacheEntry(SVDBFileIndexCacheEntry info) {
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
			fCacheSize--;
		}
	}
	
	void moveElementToCachedTail(SVDBFileIndexCacheEntry info) {
		if (!info.isCached()) {
			System.out.println("moveElementToCachedTail: Error " + info.getPath() + " is not cached");
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
			return;
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
	
	private void writeBackEntry(SVDBFileIndexCacheEntry entry) {
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
	
	private void readBackEntry(SVDBFileIndexCacheEntry entry) {
		if (entry.getSVDBFileId() != -1) {
			if (entry.getSVDBFileRef() != null) {
				// Just reset the reference
				entry.setSVDBFileRef(entry.getSVDBFileRef());
			} else {
				readBackSVDBFile(entry);
			}
		}
	
		if (entry.getSVDBPreProcFileId() != -1) {
			if (entry.getSVDBPreProcFileRef() != null) {
				// Just reset the reference
				entry.setSVDBPreProcFileRef(entry.getSVDBPreProcFileRef());
			} else {
				readBackSVDBPreProcFile(entry);
			}
		}
		
		if (entry.getSVDBFileTreeId() != -1) {
			if (entry.getSVDBFileTreeRef() != null) {
				entry.setSVDBFileTreeRef(entry.getSVDBFileTreeRef());
			} else {
				readBackSVDBFileTree(entry);
			}
		}
		
		if (entry.getMarkersId() != -1) {
			if (entry.getMarkersRef() != null) {
				entry.setMarkersRef(entry.getMarkersRef());
			} else {
				readBackMarkers(entry);
			}
		}
	}
	
	private void writeBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBFileId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getSVDBFileId());
			}
			IDBWriter writer = allocWriter();
			SVDBFile file = entry.getSVDBFileRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFile.class, file);
			
			int file_id = fFileSystem.writeFile(data_out);
			
			entry.setSVDBFileId(file_id);
			
			freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}

	private void readBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = allocReader();
			SVDBFile file = new SVDBFile();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(entry.getSVDBFileId());
			reader.init(data_in);
			reader.readObject(null, SVDBFile.class, file);
			
			entry.setSVDBFileRef(file);
			
			freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}

	private void writeBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBPreProcFileId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getSVDBPreProcFileId());
			}
			IDBWriter writer = allocWriter();
			SVDBFile file = entry.getSVDBPreProcFileRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFile.class, file);
			
			int file_id = fFileSystem.writeFile(data_out);
			
			entry.setSVDBPreProcFileId(file_id);
			
			freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}
	
	private void readBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = allocReader();
			SVDBFile file = new SVDBFile();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getSVDBPreProcFileId());
			reader.init(data_in);
			reader.readObject(null, SVDBFile.class, file);
			
			entry.setSVDBPreProcFileRef(file);
			
			freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}	
	
	private void writeBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBFileTreeId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getSVDBFileTreeId());
			}
			IDBWriter writer = allocWriter();
			SVDBFileTree file = entry.getSVDBFileTreeRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFileTree.class, file);
			
			int file_id = fFileSystem.writeFile(data_out);
			
			entry.setSVDBFileId(file_id);
			
			freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}
	
	private void readBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = allocReader();
			SVDBFileTree ft = new SVDBFileTree();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getSVDBFileTreeId());
			reader.init(data_in);
			reader.readObject(null, SVDBFileTree.class, ft);
			
			entry.setSVDBFileTreeRef(ft);
			
			freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}
	
	private void writeBackMarkers(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getMarkersId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getMarkersId());
			}
			IDBWriter writer = allocWriter();
			List<SVDBMarker> markers = entry.getMarkersRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeItemList(markers);
			
			int file_id = fFileSystem.writeFile(data_out);
			
			entry.setMarkersId(file_id);
			
			freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}	

	@SuppressWarnings("unchecked")
	private void readBackMarkers(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = allocReader();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getMarkersId());
			reader.init(data_in);
			List<SVDBMarker> markers = (List<SVDBMarker>)reader.readItemList(null);
			
			entry.setMarkersRef(markers);
			
			freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during readback", e);
		} catch (DBFormatException e) {
			fLog.error("DBWrite Exception during readback", e);
		}
	}
}
