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
package org.sveditor.core.db.index.cache.delegating;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBFileTree;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.sveditor.core.db.index.cache.file.SVDBFileIndexCacheEntry;
import org.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.sveditor.core.db.index.cache.file.SVDBFileSystemDataInput;
import org.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;
import org.sveditor.core.db.persistence.DBFormatException;
import org.sveditor.core.db.persistence.DBWriteException;
import org.sveditor.core.db.persistence.IDBReader;
import org.sveditor.core.db.persistence.IDBWriter;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

public class SVDBSegmentedIndexCache implements ISVDBIndexCache {
	private static final int										FILE_ID    = 0;
	private static final int										ARGFILE_ID = 1;

	private LogHandle												fLog;
	private SVDBSegmentedIndexCacheMgr								fCacheMgr;
	private int														fCacheId;
	private String													fProjectName;
	private String													fBaseLocation;
	private Object													fIndexData;
	private SVDBFileSystemDataInput									fIndexDataIn;
	private SVDBFileSystem											fFileSystem;

	/**
	 * Map from the 
	 */
	private Map<String, SVDBFileIndexCacheEntry>					fCache;
	private boolean													fCacheLoaded;
	
	public SVDBSegmentedIndexCache(
			SVDBSegmentedIndexCacheMgr 	mgr, 
			int 						id,
			String						project_name,
			String						base_location) {
		fLog = LogFactory.getLogHandle("SVDBSegmentedIndexCache");
		fCacheMgr = mgr;
		fCacheId = id;
		fProjectName = project_name;
		fBaseLocation = base_location;
		fCache = new HashMap<String, SVDBFileIndexCacheEntry>();
		fCacheLoaded = false;
	}
	
	public void setFS(SVDBFileSystem fs) {
		fFileSystem = fs;
	}
	
	public SVDBFileSystem getFS() {
		return fFileSystem;
	}
	
	public void write(SVDBFileSystemDataOutput dos) throws IOException, DBWriteException {
		dos.writeInt(fCacheId);
		dos.writeString(fProjectName);
		dos.writeString(fBaseLocation);
		
		// TODO: Must determine the lifetime of cache data

		if (fIndexData != null) {
			IDBWriter writer = fCacheMgr.allocWriter();
			SVDBFileSystemDataOutput ud_dos = new SVDBFileSystemDataOutput();
			
			writer.init(ud_dos);
			writer.writeObject(fIndexData.getClass(), fIndexData);
			
			fCacheMgr.freeWriter(writer);
			
			int length = 0;
			for (int i=0; i<ud_dos.getPages().size(); i++) {
				length += ud_dos.getPage(i).length;
			}
			dos.writeInt(length);
			
			for (int i=0; i<ud_dos.getPages().size(); i++) {
				dos.write(ud_dos.getPage(i));
			}
		} else {
			dos.writeInt(-1);
		}
	}
	
	public static SVDBSegmentedIndexCache read(
			SVDBSegmentedIndexCacheMgr		mgr,
			SVDBFileSystemDataInput 		dis) throws IOException {
		SVDBSegmentedIndexCache ret = null;
		
		int cache_id = dis.readInt();
		String project = dis.readString();
		String baseloc = dis.readString();
		
		ret = new SVDBSegmentedIndexCache(mgr, cache_id, project, baseloc);
		
		int ud_length = dis.readInt();
		if (ud_length != -1) {
			SVDBFileSystemDataInput	in = new SVDBFileSystemDataInput();
			
			while (ud_length > 0) {
				byte tmp[] = new byte[4096];
				int read_len = (ud_length >= 4096)?4096:ud_length;
				dis.readFully(tmp, 0, read_len);
			
				in.addPage(tmp);
				ud_length -= 4096;
			}
			
			ret.fIndexDataIn = in;
		}

		return ret;
	}
	
	void deleteStorage(SVDBFileIndexCacheEntry entry) throws IOException {
		// TODO: Each index manages its own filesystem
		if (entry.getMarkersId() != -1) {
			fFileSystem.deleteFile(
					entry.getPath(), entry.getMarkersId());
			entry.setMarkersId(-1);
		}
		if (entry.getSVDBFileId() != -1) {
			fFileSystem.deleteFile(
					entry.getPath(), entry.getSVDBFileId());
			entry.setSVDBFileId(-1);
		}
		if (entry.getSVDBPreProcFileId() != -1) {
			fFileSystem.deleteFile(
					entry.getPath(), entry.getSVDBPreProcFileId());
			entry.setSVDBPreProcFileId(-1);
		}
		if (entry.getSVDBFileTreeId() != -1) {
			fFileSystem.deleteFile(
					entry.getPath(), entry.getSVDBFileTreeId());
			entry.setSVDBFileTreeId(-1);
		}			
	}
	
	void writeBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBFileId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getPath(), entry.getSVDBFileId());
			}
			IDBWriter writer = fCacheMgr.allocWriter();
			SVDBFile file = entry.getSVDBFileRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFile.class, file);
			
//			System.out.println("writeSVDBFile: " + entry.getPath() + " " + data_out.getLength());
		
			int file_id = fFileSystem.writeFile(entry.getPath(), data_out);
			
			entry.setSVDBFileId(file_id);
			
			fCacheMgr.freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}		
	}
	
	void readBackSVDBFile(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = fCacheMgr.allocReader();
			SVDBFile file = new SVDBFile();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getPath() + ":file", entry.getSVDBFileId());
			reader.init(data_in);
			reader.readObject(null, SVDBFile.class, file);
			
			entry.setSVDBFileRef(file);
			
			fCacheMgr.freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBFormat Exception during file readback " +
					entry.getPath(), e);
		}		
	}
	
	void writeBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBPreProcFileId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getPath() + ":preProcFile", entry.getSVDBPreProcFileId());
			}
			IDBWriter writer = fCacheMgr.allocWriter();
			SVDBFile file = entry.getSVDBPreProcFileRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFile.class, file);
			
			int file_id = fFileSystem.writeFile(entry.getPath() + ":preProcFile", data_out);
			
			entry.setSVDBPreProcFileId(file_id);
			
			fCacheMgr.freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}		
	}
	
	void readBackSVDBPreProcFile(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = fCacheMgr.allocReader();
			SVDBFile file = new SVDBFile();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getPath() + ":preProcFile", entry.getSVDBPreProcFileId());
			reader.init(data_in);
			reader.readObject(null, SVDBFile.class, file);
			
			entry.setSVDBPreProcFileRef(file);
			
			fCacheMgr.freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBFormat Exception during readback of PreProc File " + entry.getPath(), e);
		}		
	}
	
	void writeBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getSVDBFileTreeId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getPath() + ":fileTree", entry.getSVDBFileTreeId());
			}
			IDBWriter writer = fCacheMgr.allocWriter();
			SVDBFileTree file = entry.getSVDBFileTreeRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeObject(SVDBFileTree.class, file);
	
			int file_id = fFileSystem.writeFile(entry.getPath() + ":fileTree", data_out);
			
			entry.setSVDBFileTreeId(file_id);
			
			fCacheMgr.freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}		
	}
	
	void readBackSVDBFileTree(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = fCacheMgr.allocReader();
			SVDBFileTree ft = new SVDBFileTree();
			
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getPath() + ":fileTree", entry.getSVDBFileTreeId());
			reader.init(data_in);
			reader.readObject(null, SVDBFileTree.class, ft);
			
			entry.setSVDBFileTreeRef(ft);
			
			fCacheMgr.freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBFormatException e) {
			fLog.error("DBFormat Exception during readback of FileTree " + entry.getPath(), e);
		}		
	}
	
	void writeBackMarkers(SVDBFileIndexCacheEntry entry) {
		try {
			if (entry.getMarkersId() != -1) {
				// Free the old file
				fFileSystem.deleteFile(entry.getPath() + ":markers", entry.getMarkersId());
			}
			IDBWriter writer = fCacheMgr.allocWriter();
			List<SVDBMarker> markers = entry.getMarkersRef();
			SVDBFileSystemDataOutput data_out = new SVDBFileSystemDataOutput();
			writer.init(data_out);
			writer.writeItemList(markers);
			
			int file_id = fFileSystem.writeFile(entry.getPath() + ":markers", data_out);
			
			entry.setMarkersId(file_id);
			
			fCacheMgr.freeWriter(writer);
		} catch (IOException e) {
			fLog.error("IO Exception during writeback", e);
		} catch (DBWriteException e) {
			fLog.error("DBWrite Exception during writeback", e);
		}
	}
	
	@SuppressWarnings("unchecked")
	void readBackMarkers(SVDBFileIndexCacheEntry entry) {
		try {
			IDBReader reader = fCacheMgr.allocReader();
			SVDBFileSystemDataInput data_in = fFileSystem.readFile(
					entry.getPath() + ":markers", entry.getMarkersId());
			reader.init(data_in);
			List<SVDBMarker> markers = (List<SVDBMarker>)reader.readItemList(null);
			
			entry.setMarkersRef(markers);
			
			fCacheMgr.freeReader(reader);
		} catch (IOException e) {
			fLog.error("IO Exception during readback", e);
		} catch (DBFormatException e) {
			fLog.error("DBFormat Exception during readback of Markers " + entry.getPath(), e);
		}		
	}
	
	public ISVDBIndexCacheMgr getCacheMgr() {
		return fCacheMgr;
	}

	public int getCacheId() {
		return fCacheId;
	}
	
	public String getProjectName() {
		return fProjectName;
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}

	Map<String, SVDBFileIndexCacheEntry> getCache() {
		return fCache;
	}
	
	private synchronized SVDBFileIndexCacheEntry getCacheEntry(String path, int type, boolean add) {
		SVDBFileIndexCacheEntry entry = null;
		boolean added = false;
		
		synchronized (fCache) {
			if (!fCacheLoaded) {
				fCacheMgr.loadCache(fCacheId, fCache);
				fCacheLoaded = true;
			}
			
			entry = fCache.get(path);
			
			if (entry == null && add) {
				entry = new SVDBFileIndexCacheEntry(fCacheId, path, type);
				fCache.put(path, entry);
				added = true;
			}
		}
		
		if (added) {
			fCacheMgr.addToCachedList(entry);
		}
		
		return entry;
	}

	/**
	 * TODO: this is obsolete
	 */
	public void removeStoragePath(List<File> db_path_list) {
		// TODO Auto-generated method stub

	}

	public void setIndexData(Object data) {
//		fIndexData = data;
	}

	public Object getIndexData() {
		return fIndexData;
	}

	public boolean init(
			IProgressMonitor 	monitor, 
			Object 				index_data,
			String 				base_location) {
		fIndexData = index_data;

		if (fIndexData != null && fIndexDataIn != null) {
			IDBReader reader = fCacheMgr.allocReader();
			fIndexDataIn.reset();
			reader.init(fIndexDataIn);

			try {
				reader.readObject(null, fIndexData.getClass(), fIndexData);
				return true;
			} catch (DBFormatException e) {
				e.printStackTrace();
			} finally {
				fCacheMgr.freeReader(reader);
			}
		}
		return false;
	}

	public void initLoad(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	public void clear(IProgressMonitor monitor) {
		// Remove all cache entries
		fCache.clear();
	
		fCacheMgr.clearIndexCache(this);
	}

	public Set<String> getFileList(boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		HashSet<String> ret = new HashSet<String>();
	
		synchronized (fCache) {
			if (!fCacheLoaded) {
				fCacheMgr.loadCache(fCacheId, fCache);
				fCacheLoaded = true;
			}
			
			for (Entry<String, SVDBFileIndexCacheEntry> e : fCache.entrySet()) {
				if (e.getValue().getType() == type) {
					ret.add(e.getKey());
				}
			}
		}

		return ret;
	}

	public long getLastModified(String path) {
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, -1, false);
		
		if (entry != null) {
			return entry.getLastModified();
		} else {
			return -1;
		}
	}

	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
	
		entry.setLastModified(timestamp);
	}

	public void addFile(String path, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		/* SVDBFileIndexCacheEntry entry = */ getCacheEntry(path, type, true);
	}

	public List<SVDBMarker> getMarkers(String path) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFileIndexCacheEntry entry = null;
		
		synchronized (fCache) {
			entry = fCache.get(path);
		}
	
		if (entry != null) {
			fCacheMgr.ensureUpToDate(entry, SVDBFileIndexCacheEntry.MARKERS_MASK);
			List<SVDBMarker> mlist = entry.getMarkersRef();
			if (mlist != null) {
				markers.addAll(mlist);
			}
		}
		
		return markers;
	}

	public void setMarkers(
			String 				path, 
			List<SVDBMarker> 	markers,
			boolean 		 	is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);

		// Ensure entry is on the 'cached' list, but don't bother
		// reading back the markers. We'll be re-setting anyway
		fCacheMgr.ensureUpToDate(entry, 0);
		
		entry.setMarkersRef(markers);
	}
	
	public Map<Integer, SVDBFile> getSubFileMap(String path) {
		SVDBFileIndexCacheEntry entry = null;
		Map<Integer, SVDBFile> ret = null;
		
		synchronized (fCache) {
			entry = fCache.get(path);
		}
		
		if (entry != null) {
			fCacheMgr.ensureUpToDate(entry, SVDBFileIndexCacheEntry.SUBFILES_MASK);
			Map<Integer, SVDBFile> map = entry.getSubFileMapRef();
			if (map != null) {
				ret = new HashMap<Integer, SVDBFile>();
				ret.putAll(map);
			}
		}
		
		return ret;
	}
	
	public void setSubFileMap(String path, Map<Integer, SVDBFile> map) {
		SVDBFileIndexCacheEntry entry = null;
		synchronized (fCache) {
			entry = fCache.get(path);
		}
		
		if (entry != null) {
			entry.setSubFileMapRef(map);
		}
	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, FILE_ID, false);
		SVDBFile file = null;
		
		if (entry != null) {
			fCacheMgr.ensureUpToDate(entry, SVDBFileIndexCacheEntry.SVDB_PREPROC_FILE_MASK);
			file = entry.getSVDBPreProcFileRef();
		}
		
		return file;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, FILE_ID, true);
		
		fCacheMgr.ensureUpToDate(entry, 0);

		entry.setPreProcFile(file);
	}

	public SVDBFileTree getFileTree(
			IProgressMonitor monitor, 
			String path,
			boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, false);
		SVDBFileTree ft = null;
		
		if (entry != null) {
			fCacheMgr.ensureUpToDate(entry, SVDBFileIndexCacheEntry.SVDB_FILETREE_MASK);
			ft = entry.getSVDBFileTreeRef();
		}
		
		return ft;
	}

	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.ensureUpToDate(entry, 0);

		entry.setFileTree(file);
	}

	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		SVDBFileIndexCacheEntry entry;
		
		if ((entry = getCacheEntry(path, FILE_ID, false)) == null) {
			entry = getCacheEntry(path, ARGFILE_ID, false);
		}
		
		if (entry == null) {
			return null;
		} else {
			// Load the file
			fCacheMgr.ensureUpToDate(entry, SVDBFileIndexCacheEntry.SVDB_FILE_MASK);
			return entry.getSVDBFileRef();
		}
	}

	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.ensureUpToDate(entry, 0);

		entry.setFile(file);
	}
	

	public void removeFile(String path, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.removeEntry(entry);
		fCache.remove(path);
	}
	
	public FileType getFileType(String path) {
		FileType ret = FileType.Invalid;
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, 0, false);
		
		if (entry != null) {
			if (entry.getType() == ARGFILE_ID) {
				ret = FileType.ArgFile; 
			} else if (entry.getType() == FILE_ID) {
				ret = FileType.SVFile;
			}
		}
		
		return ret;
	}

	public void sync() {
		// Ensure all entries associated with this cache are
		// synchronized with the filesystem
		fCacheMgr.sync(this);
	}

	public void dispose() {
		// Remove this index from the cache manager
		fCacheMgr.removeIndexCache(this);
		try {
			fFileSystem.delete();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
