package net.sf.sveditor.core.db.index.cache.file;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileIndexCache implements ISVDBIndexCache {
	private static final int										FILE_ID    = 0;
	private static final int										ARGFILE_ID = 1;
	
	private SVDBFileIndexCacheMgr									fCacheMgr;
	private int														fCacheId;
	private String													fProjectName;
	private String													fBaseLocation;
	private Object													fIndexData;
	private SVDBFileSystemDataInput									fIndexDataIn;

	/**
	 * Map from the 
	 */
	private Map<String, SVDBFileIndexCacheEntry>					fCache;
	private boolean													fCacheLoaded;
	
	public SVDBFileIndexCache(
			SVDBFileIndexCacheMgr 	mgr, 
			int 					id,
			String					project_name,
			String					base_location) {
		fCacheMgr = mgr;
		fCacheId = id;
		fProjectName = project_name;
		fBaseLocation = base_location;
		fCache = new HashMap<String, SVDBFileIndexCacheEntry>();
		fCacheLoaded = false;
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
	
	public static SVDBFileIndexCache read(
			SVDBFileIndexCacheMgr			mgr,
			SVDBFileSystemDataInput 		dis) throws IOException {
		SVDBFileIndexCache ret = null;
		
		int cache_id = dis.readInt();
		String project = dis.readString();
		String baseloc = dis.readString();
		
		ret = new SVDBFileIndexCache(mgr, cache_id, project, baseloc);
		
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
	
	synchronized SVDBFileIndexCacheEntry getCacheEntry(String path, int type, boolean add) {
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
	}

}
