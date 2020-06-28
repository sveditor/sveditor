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
package org.eclipse.hdt.sveditor.core.db.index.argfile;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTreeMacroList;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBDeclCache;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexStats;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.preproc.ISVPreProcFileMapper;
import org.eclipse.hdt.sveditor.core.preproc.ISVPreProcIncFileProvider;

/**
 * Collects data used during index parsing. A new instance of this class is
 * created for each build operation. Things managed by this class include
 * <ul>
 * <li>File IDs -- both for full and incremental build</li>
 * <li>Include-file search
 * 		<ul>
 * 		<li>Data comes from index cache</li>
 * 		<li>Build up some context information that should increase search efficiency</li>
 * 		</ul>
 * </li>
 * <li>Statistics for the last build operation</li>
 * </ul>
 * 
 * TODO:
 * <ul>
 * <li>Determine whether addFileDir adds value</li>
 * <li>Determine whether fMissingIncludes add value</li>
 * </ul>
 * @author ballance
 *
 */
public class SVDBArgFileIndexBuildData implements 
	ISVDBArgFileIndexBuildData, ISVPreProcFileMapper, ISVPreProcIncFileProvider {

	private ISVDBFileSystemProvider				fFileSystemProvider;
	private SVDBArgFileIndexCacheData			fIndexCacheData;
	private ISVDBIndexCache						fCache;
//	private Set<String>							fFileDirs;
//	private Set<String>							fMissingIncludes;
	private SVDBIndexStats						fIndexStats;
//	private SVDBLexerListenerRefCollector		fRefCollector;
	private LogHandle							fLog = LogFactory.getLogHandle("SVDBArgFileIndexBuildData");

	/**
	 * Fields used to find include files
	 */
	// Map of leaf file to resolved include directory
	private static boolean				fEnableIncludeCache = true;
	private Map<String, String>			fIncludeMap;
	private List<String>				fResolvedIncDirs;
	private List<Set<String>>			fIncDirFiles;
	private List<Set<String>>			fIncDirDirs;
	private Set<String>					fFailedSearches;
	private boolean						fIncludeCacheValid = false;	
	private List<Tuple<String, String>>	fIncludeFileList = new ArrayList<Tuple<String,String>>();
	
	public SVDBArgFileIndexBuildData(ISVDBIndexCache cache, String base_location) {
		fCache = cache;
		
//		fFileDirs = new HashSet<String>();
//		fMissingIncludes = new HashSet<String>();
		fIndexCacheData = new SVDBArgFileIndexCacheData(base_location);
	
		// Initializes the content of fIndexCacheData from the cache
		fCache.init(new NullProgressMonitor(), fIndexCacheData, base_location);
		fIndexStats = new SVDBIndexStats();
//		fRefCollector = new SVDBLexerListenerRefCollector();
		
		fIncludeMap = new HashMap<String, String>();
		fResolvedIncDirs = new ArrayList<String>();
		fIncDirFiles = new ArrayList<Set<String>>();
		fIncDirDirs = new ArrayList<Set<String>>();
		fFailedSearches = new HashSet<String>();		
	}
	
	public String getBaseLocation() {
		return fIndexCacheData.getBaseLocation();
	}
	
	public boolean containsFile(String path, int attr) {
		return fIndexCacheData.containsFile(path, attr);
	}
	
	public SVDBIndexStats getIndexStats() {
		return fIndexStats;
	}
	
	public SVDBArgFileIndexCacheData getIndexCacheData() {
		return fIndexCacheData;
	}
	
	public void setIndexCacheData(SVDBArgFileIndexCacheData data) {
		// TODO: Should we check if an existing one exists?
		fIndexCacheData = data;
	}
	
	public List<String> getFileList(int flags) {
		return fIndexCacheData.getFileList(flags);
	}
	
	public Map<String, List<SVDBDeclCacheItem>> getPackageCacheMap() {
		return fIndexCacheData.getPackageCacheMap();
	}
	
	public ISVDBIndexCacheMgr getCacheMgr() {
		return fCache.getCacheMgr();
	}
	
	public ISVDBFileSystemProvider getFSProvider() {
		return fFileSystemProvider;
	}
	
	public void setFSProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
	}
	
	public int getNumSrcFiles() {
		return fIndexCacheData.fSrcFileList.size();
	}

	/**
	 * Transfer data from <em>build_data</em> to this build data.
	 * <ul>
	 * <li>After this method completes, the build_data passed in is invalid.</li>
	 * <li>After this method completes, the state of <em>this</em> is 
	 * completely replaced by the state of <em>build_data</em>.</li>
	 * </ul>
	 *
	 * This method is typically used to update the index BuildData after
	 * a full build
	 * 
	 * @param build_data
	 */
	public void apply(SVDBArgFileIndexBuildData build_data) {
		ISVDBIndexCache old_cache = fCache;
	
		fFileSystemProvider = build_data.fFileSystemProvider;
		fIndexCacheData = build_data.fIndexCacheData;
		fCache = build_data.fCache;
//		fFileDirs = build_data.fFileDirs;
//		fMissingIncludes = build_data.fMissingIncludes;
		fIndexStats = build_data.fIndexStats;
		
		fIncludeMap = build_data.fIncludeMap;
		fResolvedIncDirs = build_data.fResolvedIncDirs;
		fIncDirFiles = build_data.fIncDirFiles;
		fIncDirDirs = build_data.fIncDirDirs;
		fFailedSearches = build_data.fFailedSearches;
		fIncludeFileList = build_data.fIncludeFileList;
		fIncludeCacheValid = build_data.fIncludeCacheValid;
		
		// We've transferred the cache to this build data
		build_data.fCache = null;

		// Free the entries in the old cache
		old_cache.dispose();
	}
	
	public void addFile(String path, boolean is_argfile) {
		fLog.debug("addFile: " + path + " is_argfile=" + is_argfile);
		long last_modified = fFileSystemProvider.getLastModifiedTime(path);
		fCache.addFile(path, is_argfile);
		fCache.setLastModified(path, last_modified, is_argfile);
		
		if (!is_argfile) {
			fIndexCacheData.addFile(path, 
					ISVDBDeclCache.FILE_ATTR_SRC_FILE+
					ISVDBDeclCache.FILE_ATTR_ROOT_FILE);
		}

		addFileDir(path);		
	}
	
	public int getFileAttr(String path) {
		return fIndexCacheData.getFileAttr(path);
	}
	
	public void addFile(String path, int attr) {
		fIndexCacheData.addFile(path, attr);
	}
	
	public void removeFile(String path, boolean is_argfile) {
		fCache.removeFile(path, is_argfile);
	}
	
	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		return fCache.getFile(monitor, path);
	}
	
	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		fCache.setFile(path, file, is_argfile);
	}
	
	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		fCache.setLastModified(path, timestamp, is_argfile);
	}
	
	public void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile) {
		fCache.setMarkers(path, markers, is_argfile);
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		return fCache.getMarkers(path);
	}
	
	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		fCache.setFileTree(path, file, is_argfile);
	}

	public void addLibFile(String path) {
		fLog.debug("addLibFile: " + path);
		long last_modified = fFileSystemProvider.getLastModifiedTime(path);
		fCache.addFile(path, false);
		fCache.setLastModified(path, last_modified, false);
		
		fIndexCacheData.addFile(path, 
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_LIB_FILE);

		addFileDir(path);
	}

	/**
	 * Doesn't appear that fFileDirs is used at all here
	 * @param file_path
	 */
	public void addFileDir(String file_path) {
		File f = new File(file_path);
		File p = f.getParentFile();

//		if (p != null && !fFileDirs.contains(p.getPath())) {
//			fFileDirs.add(p.getPath());
//		}
	}
	
	public ISVDBIndexCache getCache() {
		return fCache;
	}

	/**
	 * Clean up after this data. This is typically 
	 */
	public void dispose() {
		if (fCache != null) {
			fCache.dispose();
		}
	}

	/**
	 * Initializes the file list, so the file mapper returns 
	 * correct IDs during an incremental build. 
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

	public void addIncludePath(String path) {
		fIndexCacheData.addIncludePath(path);
		fIncludeCacheValid = false;
	}
	
	public List<String> getIncludePathList() {
		return fIndexCacheData.getIncludePaths();
	}
	
	public Map<String, List<String>> getRootIncludeMap() {
		return fIndexCacheData.fRootIncludeMap;
	}
	
	public void addDefine(String key, String val) {
		fIndexCacheData.addDefine(key, val);
	}
	
	public void setMFCU() {
		fIndexCacheData.fMFCU = true;
	}
	
	public boolean isMFCU() {
		return fIndexCacheData.fMFCU;
	}
	
	public boolean getForceSV() {
		return fIndexCacheData.fForceSV;
	}
	
	public void setForceSV(boolean force) {
		fIndexCacheData.fForceSV = force;
	}
	
	public void addArgFilePath(String path) {
		fIndexCacheData.addFile(path, ISVDBDeclCache.FILE_ATTR_ARG_FILE);
	}
	
	public void addArgFile(SVDBFile argfile) {
		fIndexCacheData.fArgFiles.add(argfile);
	}
	
	List<String> getRootFileList() {
		return fIndexCacheData.getFileList(ISVDBDeclCache.FILE_ATTR_ROOT_FILE);
	}
	
	Map<String, String> getGlobalDefines() {
		return fIndexCacheData.fGlobalDefines;
	}
	
	public void clearGlobalDefines() {
		fIndexCacheData.clearGlobalDefines();
	}
	
	public void setGlobalDefine(String key, String val) {
		fIndexCacheData.setGlobalDefine(key, val);
	}
	
	Map<String, String> getDefines() {
		return fIndexCacheData.fDefineMap;
	}
	
	Map<String, List<SVDBDeclCacheItem>> getDeclCacheMap() {
		return fIndexCacheData.getDeclCacheMap();
	}

	public Map<String, List<Integer>> getReferenceCacheMap() {
		return fIndexCacheData.getReferenceCacheMap();
	}
	
	public void setFileAttrBits(String path, int attr) {
		fIndexCacheData.setFileAttrBits(path, attr);
	}
	
	public void clrFileAttrBits(String path, int attr) {
		fIndexCacheData.clrFileAttrBits(path, attr);
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
	
	public Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(String incfile) {
		Tuple<String, List<SVDBFileTreeMacroList>> ret = null;
		
		if (!fEnableIncludeCache) {
			return ret;
		}
		
		SVDBFileTree ft_root = null;
		String incfile_fullpath = null;
		for (Tuple<String, String> e : fIncludeFileList) {
			if (e.first().endsWith(incfile)) {
				String try_path = e.first();
				boolean matches = false;
				if (try_path.length() > incfile.length()) {
					int prev_ch = try_path.charAt(try_path.length()-incfile.length()-2);
					if (prev_ch == '/' || prev_ch == '\\') {
						matches = true;
					}
				} else if (try_path.length() == incfile.length() && try_path.equals(incfile)) {
					matches = true;
				}

				if (matches) {
					ft_root = fCache.getFileTree(new NullProgressMonitor(), e.second(), false);
					incfile_fullpath = e.first();
					break;
				}
			}
		}
		
		if (ft_root != null) {
			List<SVDBFileTreeMacroList> macroset = new ArrayList<SVDBFileTreeMacroList>();
			// Locate the include file and collect the contributed macros
			if (collectMacroSet(macroset, ft_root, incfile_fullpath)) {
				ret = new Tuple<String, List<SVDBFileTreeMacroList>>(incfile_fullpath, macroset);
			}
		}
		
		return ret;
	}
	
	private boolean collectMacroSet(
			List<SVDBFileTreeMacroList> macroset,
			SVDBFileTree				ft,
			String						incfile_fullpath) {
		boolean ret = false;

		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			if (ft_i.getFilePath().equals(incfile_fullpath)) {
				ret = true;
				
				// collect the macros from this inclusion
				collectMacroSet(macroset, ft);
				break;
			} else if ((ret = collectMacroSet(macroset, ft_i, incfile_fullpath))) {
				break;
			}
		}
			
		return ret;
	}
	
	private void collectMacroSet(
			List<SVDBFileTreeMacroList> macroset,
			SVDBFileTree				ft) {
		macroset.addAll(ft.fMacroSetList);
		
		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			collectMacroSet(macroset, ft_i);
		}
	}
	
	public void addCachedIncFile(String incfile, String rootfile) {
		if (fEnableIncludeCache) {
			boolean have = false;
			for (Tuple<String, String> e : fIncludeFileList) {
				if (e.first().equals(incfile)) {
					have = true;
					break;
				}
			}

			if (!have) {
				fIncludeFileList.add(new Tuple<String, String>(incfile, rootfile));
			}
		}
	}

	// PreProcIncludeFileProvider API
	public Tuple<String, InputStream> findIncFile(String incfile) {
		Tuple<String, InputStream> ret = null;
		
		if (!fIncludeCacheValid) {
			buildIncludeCache();
		}
		
		if (incfile.length() >= 2 && incfile.charAt(0) == '.' &&
				(incfile.charAt(1) == '/' || incfile.charAt(1) == '\\')) {
			// starts with ./
			// Treat as a regular relative path
			incfile = incfile.substring(2);
		}
		
		if (fIncludeMap.containsKey(incfile)) {
			// Already have a candidate
			String path = fIncludeMap.get(incfile);
			InputStream in = fFileSystemProvider.openStream(path);
			ret = new Tuple<String, InputStream>(path, in);
		} else if (!fFailedSearches.contains(incfile)) {
			// Need to look a bit harder, then. Could be a include-relative path
			String first_elem = SVFileUtils.getPathFirstElem(incfile);
			
			// Search through all the leaf directories
			if (incfile.contains("..")) {
				fLog.debug("findIncFile: " + incfile);
				// relative path
				for (int i=0; i<fResolvedIncDirs.size(); i++) {
					String try_path = fResolvedIncDirs.get(i) + "/" + incfile;
					fLog.debug("  Resolve Path: " + try_path);
					try_path = SVFileUtils.resolvePath(try_path, 
							fResolvedIncDirs.get(i), fFileSystemProvider, true);
					fLog.debug("  Resolved Path: " + try_path);
					
					InputStream in = fFileSystemProvider.openStream(try_path);
					
					if (in != null) {
						ret = new Tuple<String, InputStream>(try_path, in);
						fIncludeMap.put(incfile, try_path);
					}
				}
			} else {
				for (int i=0; i<fResolvedIncDirs.size(); i++) {
					String try_path = null;
					if (first_elem.equals(incfile)) {
						try_path = fResolvedIncDirs.get(i) + "/" + incfile;
					} else {
						if (fIncDirDirs.get(i).contains(first_elem)) {
							try_path = fResolvedIncDirs.get(i) + "/" + incfile;
						}
					}
					
					if (try_path != null) {
						InputStream in = fFileSystemProvider.openStream(try_path);
					
						if (in != null) {
							ret = new Tuple<String, InputStream>(try_path, in);
							fIncludeMap.put(incfile, try_path);
						} else {
							try_path = SVFileUtils.resolvePath(try_path, 
								fResolvedIncDirs.get(i), fFileSystemProvider, true);
							in = fFileSystemProvider.openStream(try_path);
						
							if (in != null) {
								ret = new Tuple<String, InputStream>(try_path, in);
								fIncludeMap.put(incfile, try_path);
							}
						}
					}
					
					if (ret != null) {
						break;
					}
				}
			}
		
			// Absolute path
			if (ret == null && incfile.length() >= 2 && (incfile.charAt(0) == '/' || 
					(Character.isAlphabetic(incfile.charAt(0)) && incfile.charAt(1) == ':'))) {
				InputStream in = fFileSystemProvider.openStream(incfile);
				if (in != null) {
					ret = new Tuple<String, InputStream>(incfile, in);
				}
			}
			
			if (ret == null) {
				fFailedSearches.add(incfile);
			}
		}
		
		/*
		for (String path : fIndexCacheData.fIncludePathList) {
			String fullpath = SVFileUtils.resolvePath(incfile, path, fFileSystemProvider, true);
			if (fFileSystemProvider.fileExists(fullpath)) {
				InputStream in = fFileSystemProvider.openStream(fullpath);
				return new Tuple<String, InputStream>(fullpath, in);
			}
		}	
		 */

		return ret;
	}

	private void buildIncludeCache() {
		fIncludeMap.clear();
		fResolvedIncDirs.clear();
		fIncDirFiles.clear();
		fIncDirDirs.clear();
		fFailedSearches.clear();
	
		for (String inc_dir : fIndexCacheData.fIncludePathList) {
			addIncDir(inc_dir);
		}
		
		fIncludeCacheValid = true;
	}
	
	private void addIncDir(String inc_dir) {
		String resolved_inc_dir = SVFileUtils.resolvePath(
				inc_dir, inc_dir, fFileSystemProvider, true);
		
		fLog.debug("addIncDir: " + inc_dir + " => " + resolved_inc_dir);
		
		Set<String> inc_dir_files = new HashSet<String>();
		Set<String> inc_dir_dirs = new HashSet<String>();
		
		// List all elements in the directory
		if (fFileSystemProvider.isDir(resolved_inc_dir)) {
			List<String> fd_l = fFileSystemProvider.getFiles(resolved_inc_dir);
			
			for (String fd : fd_l) {
				if (fFileSystemProvider.isDir(fd)) {
					inc_dir_dirs.add(SVFileUtils.getPathLeaf(fd));
				} else {
					String leaf = SVFileUtils.getPathLeaf(fd);
					inc_dir_files.add(leaf);
					
//					if (!fIncludeMap.containsKey(leaf)) {
//						fIncludeMap.put(leaf, fd);
//					}
				}
			}
		}

		fResolvedIncDirs.add(resolved_inc_dir);
		fIncDirFiles.add(inc_dir_files);
		fIncDirDirs.add(inc_dir_dirs);		
	}
	
}



