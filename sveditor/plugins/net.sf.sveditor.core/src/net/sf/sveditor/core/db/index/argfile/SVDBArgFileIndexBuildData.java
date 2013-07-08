package net.sf.sveditor.core.db.index.argfile;

import java.io.InputStream;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;

public class SVDBArgFileIndexBuildData implements 
	ISVPreProcFileMapper, ISVPreProcIncFileProvider {

	ISVDBFileSystemProvider						fFileSystemProvider;
	SVDBArgFileIndexCacheData					fIndexCacheData;
	ISVDBIndexCache								fCache;
	ISVDBIndexCacheMgr							fCacheMgr;
	Set<String>									fFileDirs;
	Set<String>									fMissingIncludes;
	
	public SVDBArgFileIndexBuildData(ISVDBIndexCache cache, String base_location) {
		fCache = cache;
		fCacheMgr = cache.getCacheMgr();
		
		fFileDirs = new HashSet<String>();
		fMissingIncludes = new HashSet<String>();
		fIndexCacheData = new SVDBArgFileIndexCacheData(base_location);
		
		fCache.init(new NullProgressMonitor(), fIndexCacheData, base_location);
	}
	
	void apply(SVDBArgFileIndexBuildData build_data) {
		ISVDBIndexCache old_cache = fCache;
//		ISVDBIndexCacheMgr old_cache_mgr = fCacheMgr;
	
		fFileSystemProvider = build_data.fFileSystemProvider;
		fIndexCacheData = build_data.fIndexCacheData;
		fCache = build_data.fCache;
		fCacheMgr = build_data.fCacheMgr;
		fFileDirs = build_data.fFileDirs;
		fMissingIncludes = build_data.fMissingIncludes;
	
		// We've transferred the cache to this build data
		build_data.fCache = null;

		// Free the entries in the old cache
		old_cache.dispose();
	}

	/**
	 * Clean up after this data. This is typically 
	 */
	void dispose() {
		if (fCache != null) {
			fCache.dispose();
		}
	}

	/**
	 * Initializes the file list, so the file mapper returns 
	 * correct IDs during an incremental build
	 * 
	 * @param other
	 */
	void initFileMapperState(SVDBArgFileIndexBuildData other) {
		fIndexCacheData.fSrcFileList.clear();
		fIndexCacheData.fSrcFileAttr.clear();
		for (int i=0; i<other.fIndexCacheData.fSrcFileList.size(); i++) {
			fIndexCacheData.fSrcFileList.add(other.fIndexCacheData.fSrcFileList.get(i));
			fIndexCacheData.fSrcFileAttr.add(other.fIndexCacheData.fSrcFileAttr.get(i));
		}
		fIndexCacheData.fIncludePathList.clear();
		fIndexCacheData.fIncludePathList.addAll(other.fIndexCacheData.fIncludePathList);
	}

	void addIncludePath(String path) {
		fIndexCacheData.addIncludePath(path);
	}
	
	void addDefine(String key, String val) {
		fIndexCacheData.addDefine(key, val);
	}
	
	void setMFCU() {
		fIndexCacheData.fMFCU = true;
	}
	
	boolean isMFCU() {
		return fIndexCacheData.fMFCU;
	}
	
	void addArgFilePath(String path) {
		fIndexCacheData.addFile(path, ISVDBDeclCache.FILE_ATTR_ARG_FILE);
	}
	
	void addArgFile(SVDBFile argfile) {
		fIndexCacheData.fArgFiles.add(argfile);
	}
	
	List<String> getRootFileList() {
		return fIndexCacheData.fRootFileList;
	}
	
	Map<String, String> getGlobalDefines() {
		return fIndexCacheData.fGlobalDefines;
	}
	
	Map<String, String> getDefines() {
		return fIndexCacheData.fDefineMap;
	}
	
	Map<String, List<SVDBDeclCacheItem>> getDeclCacheMap() {
		return fIndexCacheData.getDeclCacheMap();
	}

	// FileMapper API
	public int mapFilePathToId(String path, boolean add) {
		int idx = (fIndexCacheData.fSrcFileList.indexOf(path)+1);
		
		if (idx < 1 && add) {
			idx = (fIndexCacheData.fSrcFileList.size()+1);
//			fLog.debug("Register file \"" + path + "\" as file id " + idx);
			fIndexCacheData.addFile(path, ISVDBDeclCache.FILE_ATTR_SRC_FILE);
		}
		
		return idx;		
	}

	public String mapFileIdToPath(int id) {
		if (id > 0 && id <= fIndexCacheData.fSrcFileList.size()) {
			return fIndexCacheData.fSrcFileList.get(id-1);
		}
		
		return null;		
	}

	// PreProcIncludeFileProvider API
	public Tuple<String, InputStream> findIncFile(String incfile) {
		for (String path : fIndexCacheData.fIncludePathList) {
			String fullpath = SVFileUtils.resolvePath(incfile, path, fFileSystemProvider, true);
			if (fFileSystemProvider.fileExists(fullpath)) {
				InputStream in = fFileSystemProvider.openStream(fullpath);
				return new Tuple<String, InputStream>(fullpath, in);
			}
		}		

		return null;
	}
	
}
