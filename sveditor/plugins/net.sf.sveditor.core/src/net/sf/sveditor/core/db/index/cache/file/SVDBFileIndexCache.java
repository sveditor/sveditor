package net.sf.sveditor.core.db.index.cache.file;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileIndexCache implements ISVDBIndexCache {
	private static final int										FILE_ID    = 0;
	private static final int										ARGFILE_ID = 1;
	
	private SVDBFileIndexCacheMgr									fCacheMgr;
	private int														fCacheId;
	private String													fProjectName;
	private String													fBaseLocation;
	private Object													fIndexData;
	/**
	 * Map from the 
	 */
	private Map<String, SVDBFileIndexCacheEntry>					fCache;
	
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
			entry = fCache.get(path);
			
			if (entry == null && add) {
				entry = new SVDBFileIndexCacheEntry(path, type);
				fCache.put(path, entry);
				added = true;
			}
		}
		
		if (added) {
			entry.setCached();
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
		fIndexData = data;
	}

	public Object getIndexData() {
		return fIndexData;
	}

	public boolean init(IProgressMonitor monitor, Object index_data,
			String base_location) {
		// TODO Auto-generated method stub
		return false;
	}

	public void initLoad(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	public void clear(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	public Set<String> getFileList(boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		HashSet<String> ret = new HashSet<String>();
	
		synchronized (fCache) {
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
//			fCacheMgr.ensureUpToDate(entry);
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

		fCacheMgr.ensureUpToDate(entry);
		
		entry.setMarkersRef(markers);
	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, FILE_ID, false);
		SVDBFile file = null;
		
		if (entry != null) {
			fCacheMgr.ensureUpToDate(entry);
			file = entry.getSVDBPreProcFileRef();
		}
		
		return file;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, FILE_ID, true);
		
		fCacheMgr.ensureUpToDate(entry);

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
			fCacheMgr.ensureUpToDate(entry);
			ft = entry.getSVDBFileTreeRef();
		}
		
		return ft;
	}

	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.ensureUpToDate(entry);

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
			fCacheMgr.ensureUpToDate(entry);
			return entry.getSVDBFileRef();
		}
	}

	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.ensureUpToDate(entry);

		entry.setFile(file);
	}

	public void removeFile(String path, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);
		
		fCacheMgr.removeEntry(entry);
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
