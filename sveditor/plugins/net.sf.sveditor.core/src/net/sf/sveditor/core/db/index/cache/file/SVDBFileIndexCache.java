package net.sf.sveditor.core.db.index.cache.file;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

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
	private Map<Integer, Map<String, SVDBFileIndexCacheEntry>>		fCache;
	
	public SVDBFileIndexCache(
			SVDBFileIndexCacheMgr 	mgr, 
			int 					id,
			String					project_name,
			String					base_location) {
		fCacheMgr = mgr;
		fCacheId = id;
		fProjectName = project_name;
		fBaseLocation = base_location;
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
	
	Map<Integer, Map<String, SVDBFileIndexCacheEntry>> getCache() {
		return fCache;
	}
	
	SVDBFileIndexCacheEntry getCacheEntry(String path, int type, boolean add) {
		SVDBFileIndexCacheEntry entry = null;
		
		synchronized (fCache) {
			Map<String, SVDBFileIndexCacheEntry> c;
			if (!fCache.containsKey(type)) {
				c = new HashMap<String, SVDBFileIndexCacheEntry>();
				fCache.put(type, c);
			} else {
				c = fCache.get(type);
			}
			
			entry = c.get(path);
			
			if (entry == null && add) {
				entry = new SVDBFileIndexCacheEntry();
				c.put(path, entry);
			}
		}
		
		if (entry != null) {
			if (entry.isCached()) {
				fCacheMgr.moveElementToTail(entry);
			} else {
				fCacheMgr.addElementToTail(entry);
			}
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
		// TODO Auto-generated method stub
		return null;
	}

	public long getLastModified(String path) {
		// TODO Auto-generated method stub
		return 0;
	}

	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		// TODO Auto-generated method stub

	}

	public void addFile(String path, boolean is_argfile) {
		// TODO Auto-generated method stub

	}

	public List<SVDBMarker> getMarkers(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	public void setMarkers(
			String 				path, 
			List<SVDBMarker> 	markers,
			boolean 		 	is_argfile) {
		// TODO Auto-generated method stub

	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		// TODO Auto-generated method stub
		return null;
	}

	public void setPreProcFile(String path, SVDBFile file) {
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, FILE_ID, true);

		entry.setPreProcFile(file);
	}

	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path,
			boolean is_argfile) {
		// TODO Auto-generated method stub
		return null;
	}

	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);

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
			return null;
		}
	}

	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		int type = (is_argfile)?ARGFILE_ID:FILE_ID;
		
		SVDBFileIndexCacheEntry entry = getCacheEntry(path, type, true);

		entry.setFile(file);
	}

	public void removeFile(String path, boolean is_argfile) {
		// TODO Auto-generated method stub

	}

	public void sync() {
		// TODO Auto-generated method stub

	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

}
