/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefFinder;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBRefCacheEntry;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.refs.SVDBRefFinder;
import net.sf.sveditor.core.db.refs.SVDBRefItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex2 implements ISVDBIndex, ISVDBRefFinder,
		ILogLevelListener, ILogLevel, ISVPreProcIncFileProvider,
		ISVPreProcFileMapper {

	public String 								fProjectName;
	private IProject 							fProject;
	private String 								fBaseLocation;
	private String 								fResolvedBaseLocation;
	private String 								fBaseLocationDir;
	private SVDBArgFileIndex2LoadIndexJob		fLoadIndexJob;

	private SVDBArgFileIndexCacheData 			fIndexCacheData;
	private boolean 							fCacheDataValid;

	private Set<String> 						fMissingIncludes;

	private List<ISVDBIndexChangeListener> 		fIndexChangeListeners;

	private LogHandle fLog;
	private ISVDBFileSystemProvider 			fFileSystemProvider;

	private ISVDBIndexCache fCache;

	private SVDBIndexConfig fConfig;

	// Manages a list of the directories that managed files are stored in
	private Set<String> fFileDirs;

	private boolean fDebugEn;

	private boolean fInWorkspaceOk;

	/**
	 * True if the root file list is valid.
	 */
	private boolean	fIndexValid;
	private boolean fAutoRebuildEn;
	private boolean fIsDirty;
	
	private SVDBArgFileIndex2(String project) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fMissingIncludes = new HashSet<String>();
		fAutoRebuildEn = true;

		fFileDirs = new HashSet<String>();

		// Try to obtain the project handle
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			fProject = root.getProject(fProjectName);
		} catch (IllegalStateException e) {
			// Occurs if the workspace is closed
		}
		
		fLoadIndexJob = new SVDBArgFileIndex2LoadIndexJob(this);
	}

	public SVDBArgFileIndex2(String project, String base_location,
			ISVDBFileSystemProvider fs_provider, ISVDBIndexCache cache,
			SVDBIndexConfig config) {
		this(project);
		fBaseLocation = base_location;
		fCache = cache;
		fConfig = config;

		setFileSystemProvider(fs_provider);
		fInWorkspaceOk = (base_location.startsWith("${workspace_loc}"));
		fAutoRebuildEn = true;
	}

	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public void setEnableAutoRebuild(boolean en) {
		fAutoRebuildEn = en;
	}

	public boolean isDirty() {
		return fIsDirty;
	}

	/**
	 * Called when the index is initialized to determine whether the cached
	 * information is still valid
	 * 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private boolean checkCacheValid() {
		boolean valid = true;
		String version = SVCorePlugin.getVersion();

		if (fDebugEn) {
			fLog.debug("Cached version=" + fIndexCacheData.getVersion()
					+ " version=" + version);
		}

		if (fIndexCacheData.getVersion() == null
				|| !fIndexCacheData.getVersion().equals(version)) {
			valid = false;
			return valid;
		}

		// Confirm that global defines are the same
		if (fConfig != null) {
			// First check to see if all configured global defines are present
			if (fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = (Map<String, String>) fConfig
						.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				if (define_map.size() != fIndexCacheData.getGlobalDefines()
						.size()) {
					if (fDebugEn) {
						fLog.debug(LEVEL_MID,
								"Cache invalid -- size of global defines is different");
					}
					valid = false;
				} else {
					// Check all defines
					for (Entry<String, String> e : define_map.entrySet()) {
						if (fIndexCacheData.getGlobalDefines().containsKey(
								e.getKey())) {
							if (!fIndexCacheData.getGlobalDefines()
									.get(e.getKey()).equals(e.getValue())) {
								if (fDebugEn) {
									fLog.debug(
											LEVEL_MID,
											"Cache invalid -- define "
													+ e.getKey()
													+ " has a different value");
								}
								valid = false;
								break;
							}
						} else {
							if (fDebugEn) {
								fLog.debug(LEVEL_MID,
										"Cache invalid -- define " + e.getKey()
												+ " not in cache");
							}
							valid = false;
							break;
						}
					}
				}
			} else if (fIndexCacheData.getGlobalDefines().size() > 0) {
				// Local index has defines and the incoming config does not
				if (fDebugEn) {
					fLog.debug(LEVEL_MID,
							"Cache invalid -- no global defines, and cache has");
				}
				valid = false;
			}
		}

		if (fCache.getFileList(false).size() > 0) {
			for (String path : fCache.getFileList(false)) {
				long fs_timestamp = fFileSystemProvider
						.getLastModifiedTime(path);
				long cache_timestamp = fCache.getLastModified(path);
				if (fs_timestamp != cache_timestamp) {

					if (fDebugEn) {
						fLog.debug(LEVEL_MIN,
								"Cache is invalid due to timestamp on " + path
										+ ": file=" + fs_timestamp + " cache="
										+ cache_timestamp);
					}
					valid = false;
					break;
				}
			}
		} else {
			if (fDebugEn) {
				fLog.debug(LEVEL_MIN, "Cache " + getBaseLocation()
						+ " is invalid -- 0 entries");
			}
			SVDBIndexFactoryUtils.setBaseProperties(fConfig, this);
			valid = false;
		}

		if (getCacheData().getMissingIncludeFiles().size() > 0 && valid) {
			if (fDebugEn) {
				fLog.debug("Checking missing-include list added files");
			}
			/** TODO: 
			for (String path : getCacheData().getMissingIncludeFiles()) {
				SVDBSearchResult<SVDBFile> res = findIncludedFile(path);
				if (res != null) {
					if (fDebugEn) {
						fLog.debug(
								LEVEL_MIN,
								"Cache "
										+ getBaseLocation()
										+ " is invalid since previously-missing include file is now found: "
										+ path);
					}
					valid = false;
					break;
				}
			}
			 */
		}

		if (valid) {
			synchronized (getCache()) {
				for (String arg_file : getCache().getFileList(true)) {
					long ts = getFileSystemProvider().getLastModifiedTime(
							arg_file);
					long ts_c = getCache().getLastModified(arg_file);
					if (ts > ts_c) {
						fLog.debug("    arg_file " + arg_file + " ts=" + ts
								+ " cached ts=" + ts_c);
						return false;
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "[AbstractSVDBIndex] Cache "
					+ getBaseLocation() + " is "
					+ ((valid) ? "valid" : "invalid"));
		}

		return valid;
	}

	/**
	 * Initialize the index
	 * 
	 * @param monitor
	 */
	@SuppressWarnings("unchecked")
	public void init(IProgressMonitor monitor) {
		SubProgressMonitor m;

		monitor.beginTask("Initialize index " + getBaseLocation(), 100);

		// Initialize the cache
		m = new SubProgressMonitor(monitor, 1);
		fIndexCacheData = new SVDBArgFileIndexCacheData(getBaseLocation());
		fCacheDataValid = fCache.init(m, fIndexCacheData, fBaseLocation);

		if (fCacheDataValid) {
			fCacheDataValid = checkCacheValid();
		}

		if (fCacheDataValid) {
			if (fDebugEn) {
				fLog.debug("Cache is valid");
			}
			fIndexValid = true;

			// If we've determined the index data is valid, then we need to
			// fixup some index entries
			if (fIndexCacheData.getDeclCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : fIndexCacheData
						.getDeclCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also update the package cache
			if (fIndexCacheData.getPackageCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : fIndexCacheData
						.getPackageCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also re-set filenames on the reference cache
			if (fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : fIndexCacheData
						.getReferenceCacheMap().entrySet()) {
					e.getValue().setFilename(e.getKey());
				}
			}

			// Register all files with the directory set
			for (String f : fCache.getFileList(false)) {
				addFileDir(f);
			}
		} else {
			if (fDebugEn) {
				fLog.debug("Cache " + getBaseLocation() + " is invalid");
			}
			invalidateIndex(m, "Cache is invalid", true);
		}
		// set the version to check later
		fIndexCacheData.setVersion(SVCorePlugin.getVersion());

		// Set the global settings anyway
		if (fConfig != null
				&& fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
			Map<String, String> define_map = (Map<String, String>) fConfig
					.get(ISVDBIndexFactory.KEY_GlobalDefineMap);

			fIndexCacheData.clearGlobalDefines();
			for (String key : define_map.keySet()) {
				fIndexCacheData.setGlobalDefine(key, define_map.get(key));
			}
		}

		monitor.done();
	}

	/**
	 * 
	 */
	public synchronized void loadIndex(IProgressMonitor monitor) {
		
		invalidateIndex(monitor, "loadIndex", true);
		
		buildIndex(monitor);

		synchronized (fCache) {
			fCache.sync();
		}
		
		fIndexValid = true;		
	}

	public synchronized boolean isLoaded() {
		return fIndexValid;
	}

	public synchronized boolean isFileListLoaded() {
		return fIndexValid;
	}

	/**
	 * @param monitor
	 * @param state
	 */
	private void ensureIndexUpToDate(IProgressMonitor super_monitor) {
		SubProgressMonitor monitor = new SubProgressMonitor(super_monitor, 1);
		monitor.beginTask("Ensure Index State for " + getBaseLocation(), 4);

		if (!fIndexValid) {
			fLoadIndexJob.load();
			/*
			if (fCacheDataValid) {
				SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
				fCache.initLoad(m);
				m.done();
			} else {
				buildIndex(super_monitor);
			}
			synchronized (fCache) {
				fCache.sync();
			}
			fIndexValid = true;
			 */
		}

		monitor.done();
	}

	private void invalidateIndex(IProgressMonitor monitor, String reason,
			boolean force) {
		if (fDebugEn) {
			if (fAutoRebuildEn || force) {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: "
						+ ((reason == null) ? "No reason given" : reason));
			} else {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: "
						+ ((reason == null) ? "No reason given" : reason)
						+ " (ignored -- AutoRebuild disabled)");
			}
		}

		synchronized (this) {
			if (fAutoRebuildEn || force) {
				fIndexValid = false;
				fCacheDataValid = false;
				fIndexCacheData.clear();
				fCache.clear(monitor);
				fMissingIncludes.clear();
			} else {
				fIsDirty = true;
			}
		}
	}

	public void rebuildIndex(IProgressMonitor monitor) {
		invalidateIndex(monitor, "Rebuild Index Requested", true);
	}

	public ISVDBIndexCache getCache() {
		return fCache;
	}

	public SVDBIndexConfig getConfig() {
		return fConfig;
	}

	private SVDBBaseIndexCacheData getCacheData() {
		return fIndexCacheData;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;

		if (fFileSystemProvider != null) {
			fFileSystemProvider.init(getResolvedBaseLocationDir());
		}
	}

	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}

	public String getBaseLocation() {
		return fBaseLocation;
	}

	public String getProject() {
		return fProjectName;
	}

	public IProject getProjectHndl() {
		return fProject;
	}

	public String getResolvedBaseLocation() {
		if (fResolvedBaseLocation == null) {
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(fBaseLocation,
					fProjectName, fInWorkspaceOk);
		}

		return fResolvedBaseLocation;
	}

	public String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			String base_location = getResolvedBaseLocation();
			if (fDebugEn) {
				fLog.debug("   base_location: " + base_location);
			}
			if (fFileSystemProvider.isDir(base_location)) {
				if (fDebugEn) {
					fLog.debug("       base_location + " + base_location
							+ " is_dir");
				}
				fBaseLocationDir = base_location;
			} else {
				if (fDebugEn) {
					fLog.debug("       base_location + " + base_location
							+ " not_dir");
				}
				fBaseLocationDir = SVFileUtils.getPathParent(base_location);
				if (fDebugEn) {
					fLog.debug("   getPathParent " + base_location + ": "
							+ fBaseLocationDir);
				}
			}
		}
		return fBaseLocationDir;
	}

	public void setGlobalDefine(String key, String val) {
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "setGlobalDefine(" + key + ", " + val + ")");
		}
		fIndexCacheData.setGlobalDefine(key, val);

		// Rebuild the index when something changes
		if (!fIndexCacheData.getGlobalDefines().containsKey(key)
				|| !fIndexCacheData.getGlobalDefines().get(key).equals(val)) {
			rebuildIndex(new NullProgressMonitor());
		}
	}

	public void clearGlobalDefines() {
		fIndexCacheData.clearGlobalDefines();
	}

	private void clearDefines() {
		fIndexCacheData.clearDefines();
	}

	private void addDefine(String key, String val) {
		fIndexCacheData.addDefine(key, val);
	}

	private void clearIncludePaths() {
		fIndexCacheData.clearIncludePaths();
	}

	private void addIncludePath(String path) {
		fIndexCacheData.addIncludePath(path);
	}

	/**
	 * getFileList() -- returns a list of all source files
	 */
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		ensureIndexUpToDate(monitor);
		
		List<String> ret = new ArrayList<String>();
		synchronized (fIndexCacheData) {
			ret.addAll(fIndexCacheData.fSrcFileList);
		}
		
		return ret;
	}

	/**
	 * Implementation of ISVDBIndexIterator findFile()
	 */
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		String r_path = path;
		SVDBFile ret = null;
		SVDBFile root_file = null;
		if (fDebugEn) {
			fLog.debug("--> findFile: " + path);
		}
		ensureIndexUpToDate(monitor);
		
		root_file = findRootFile(r_path);
		
		if (root_file != null) {
			// Copy 
			int file_id = mapFilePathToId(r_path, false);
			ret = new SVDBFile(r_path);
		
			synchronized (fCache) {
				extractFileContents(ret, root_file, file_id);
			}
		}
		
		monitor.done();

		if (fDebugEn) {
			fLog.debug("--> findFile: " + path + " ret=" + ret);
		}

		return ret;
	}
	
	// Search a specific path resolution
	private SVDBFile findRootFile(String path) {
		SVDBFile ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		synchronized (fCache) {
			// Search the file tree of each root file
			for (String root_path : fCache.getFileList(false)) {
				SVDBFileTree ft = fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if (findTargetFileTree(ft, paths) != null) {
					ret = fCache.getFile(new NullProgressMonitor(), root_path);
					break;
				}
			}
		}
		
		return ret;
	}

	private SVDBFileTree findTargetFileTree(String path) {
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		synchronized (fCache) {
			// Search the file tree of each root file
			for (String root_path : fCache.getFileList(false)) {
				SVDBFileTree ft = fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if ((ret = findTargetFileTree(ft, paths)) != null) {
					break;
				}
			}
		}
		
		return ret;
	}

	/**
	 * Locate scopes to add to the target file
	 * 
	 * @param ret
	 * @param parent
	 * @param file_id
	 */
	private void extractFileContents(
			SVDBFile			ret,
			ISVDBChildParent	parent, 
			int 				file_id) {
		// indicates whether we've found the target
		// file at this scope level. We don't need to
		// traverse through any more sub-scopes once
		// we've found scopes in the target file
		boolean found_file = false;
		
		for (ISVDBChildItem c : parent.getChildren()) {
			SVDBLocation l = c.getLocation();
			if (l != null && l.getFileId() == file_id) {
				ret.addChildItem(c);
				found_file = true;
			} else if (c instanceof ISVDBChildParent) {
				if (!found_file) {
					extractFileContents(ret, (ISVDBChildParent)c, file_id);
				} else {
					break;
				}
			}
		}
	}
	
	private SVDBFileTree findTargetFileTree(SVDBFileTree ft, String paths[]) {
		SVDBFileTree ret = null;
				
		for (String path : paths) {
			if (path == null) {
				continue;
			}
			
			if (ft.getFilePath().equals(path)) {
				ret = ft;
				break;
			} else {
				for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
					if ((ret = findTargetFileTree(ft_s, paths)) != null) {
						break;
					}
				}
			}
			if (ret != null) {
				break;
			}
		}
		
		return ret;
	}
	
	private SVDBFileTree findRootFileTree(String path) {
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		List<String> root_path_l = new ArrayList<String>();
		
		synchronized (fCache) {
			root_path_l.addAll(fCache.getFileList(false));
		}

		for (String root_path : root_path_l) {
			SVDBFileTree ft = fCache.getFileTree(
					new NullProgressMonitor(), root_path, false);

			if (findTargetFileTree(ft, paths) != null) {
				ret = ft;
				break;
			}
		}
	
		return ret;
	}
	
	private SVDBFileTree findRootFileTree(SVDBFileTree parent, String paths[]) {
		for (String path : paths) {
			if (path == null) {
				continue;
			}
			
			if (parent.getFilePath().equals(path)) {
				return parent;
			} else {
				for (SVDBFileTree ft_s : parent.fIncludedFileTrees) {
					if (findRootFileTree(ft_s, paths) != null) {
						return parent;
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Implementation of ISVDBIndexIterator method
	 */
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		// TODO: Update implementation
		String r_path = path;
		SVDBFile file = null;

		ensureIndexUpToDate(monitor);

		// Cycle through the various path formats
		for (String fmt : new String[] { null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM }) {
			if (fmt != null) {
				r_path = fFileSystemProvider.resolvePath(path, fmt);
			}
			file = fCache.getPreProcFile(new NullProgressMonitor(), r_path);

			if (file != null) {
				break;
			}
		}

		return file;
	}

	public List<SVDBMarker> getMarkers(String path) {
		// TODO: Update implementation
		/* SVDBFile file = */findFile(path);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		synchronized (fCache) {
			markers.addAll(fCache.getMarkers(path));
		}

		if (fDebugEn) {
			fLog.debug("markers for " + path + ": " + markers.size());
		}

		return markers;
	}

	private void addFile(String path, boolean is_argfile) {
		fLog.debug("addFile: " + path + " is_argfile=" + is_argfile);
		synchronized (fCache) {
			fCache.addFile(path, is_argfile);
			fCache.setLastModified(path, getFileSystemProvider()
					.getLastModifiedTime(path), is_argfile);
		}
		
		if (!is_argfile) {
			synchronized (fIndexCacheData) {
				fIndexCacheData.fRootFileList.add(path);
			}
		}

		addFileDir(path);
	}

	private void addFileDir(String file_path) {
		File f = new File(file_path);
		File p = f.getParentFile();

		if (p != null && !fFileDirs.contains(p.getPath())) {
			fFileDirs.add(p.getPath());
		}
	}

	private void clearFilesList() {
		fLog.debug("clearFilesList");
		synchronized (fCache) {
			fCache.clear(new NullProgressMonitor());
		}
		synchronized (this) {
			fFileDirs.clear();
		}
		
		synchronized (fIndexCacheData) {
			fIndexCacheData.fSrcFileList.clear();
			fIndexCacheData.fRootFileList.clear();
		}
	}

	// TODO: This should probably be handled externally
	private void propagateMarkers(String path) {
		List<SVDBMarker> ml = fCache.getMarkers(path);
		getFileSystemProvider().clearMarkers(path);

		if (ml != null) {
			for (SVDBMarker m : ml) {
				String type = null;
				switch (m.getMarkerType()) {
				case Info:
					type = ISVDBFileSystemProvider.MARKER_TYPE_INFO;
					break;
				case Warning:
					type = ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
					break;
				case Error:
					type = ISVDBFileSystemProvider.MARKER_TYPE_ERROR;
					break;
				}
				getFileSystemProvider().addMarker(path, type,
						m.getLocation().getLine(), m.getMessage());
			}
		}
	}

	public SVDBSearchResult<String> findIncludedFilePath(String path) {
		String file = null;

		String res_path = SVFileUtils.resolvePath(path, 
				getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);

		if (fFileSystemProvider.fileExists(res_path)) {
			return new SVDBSearchResult<String>(res_path, this);
		}
		
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = SVFileUtils.resolvePath(inc_dir + "/" + path, 
					getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
			if (fFileSystemProvider.fileExists(inc_path)) {
				if (fDebugEn) {
					fLog.debug("findIncludedFilePath: located include \"" + path + "\"");
				}

				file = inc_path;
				break;
			}
			/*
			else {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: file \"" + inc_path
							+ "\" does not exist");
				}
			}
			 */
		}

		if (file != null) {
			if (fDebugEn) {
				fLog.debug("findIncludedFile: Found and parsed new include file");
			}
			return new SVDBSearchResult<String>(file, this);
		}

		return null;
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider provider) {
		// TODO: Unused ISVDBIndex method
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.add(l);
		}
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.remove(l);
		}
	}

	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor,
			InputStream in, String path, List<SVDBMarker> markers) {
		String r_path = SVFileUtils.resolvePath(path, getResolvedBaseLocation(), 
				fFileSystemProvider, fInWorkspaceOk);
		
		if (!fFileSystemProvider.fileExists(r_path)) {
			return null;
		}

		// TODO: should we update the index, or keep passive?
		
		// First, ensure index is up-to-date
		ensureIndexUpToDate(monitor);
		
		SVDBFileTree ft = findTargetFileTree(r_path);
		
		if (ft != null) {
			return null;
		}
		
		SVPreProcessor2 preproc = new SVPreProcessor2(
				r_path, in, null, null);
		SVPreProcOutput out = preproc.preprocess(markers);
		
		ParserSVDBFileFactory f = new ParserSVDBFileFactory();
		
		SVDBFile file = f.parse(out, r_path, markers);
		
		// Find the root file containing the target file
//		SVDBFile root_file = findRootFile(path) 
		// TODO: Implement parse
		/*
		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(null);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);

		path = SVFileUtils.normalize(path);

		SVDBFileTree file_tree = findFileTree(path, false);

		if (file_tree == null) {
			if (getFileSystemProvider().fileExists(path)) {
				// If the file does exist, but isn't included in the
				// list of discovered files, invalidate the index,
				// add the file, and try again
				invalidateIndex(new NullProgressMonitor(),
						"Failed to find FileTree for " + path, false);
				addFile(path, true);
				file_tree = findFileTree(path, false);

			} else {
				// TODO: is this really correct?
				return null;
			}
		}

		// Now, build the 'real' filetree
		file_tree = file_tree.duplicate();
		List<String> missing_includes = new ArrayList<String>();
		Set<String> included_files = new HashSet<String>();
		Map<String, SVDBFileTree> working_set = new HashMap<String, SVDBFileTree>();
		List<SVDBMarker> markers_e = new ArrayList<SVDBMarker>();
		buildPreProcFileMap(null, file_tree, missing_includes, included_files,
				working_set, markers, false);

		markers.clear();

		InputStreamCopier copier = new InputStreamCopier(in);
		in = null;

		SVPreProcDirectiveScanner sc = new SVPreProcDirectiveScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();
		sc.setObserver(ob);

		file_tree = file_tree.duplicate();

		sc.init(copier.copy(), path);
		sc.process();

		SVDBFile svdb_pp = ob.getFiles().get(0);

		if (fDebugEn) {
			fLog.debug("Processed pre-proc file");
		}

		// fFileSystemProvider.clearMarkers(file_tree.getFilePath());
		file_tree.setSVDBFile(svdb_pp);
		// addIncludeFiles(file_tree, file_tree.getSVDBFile());

		if (file_tree.getFilePath() == null) {
			System.out.println("file_tree path: " + path + " is null");
		}

		dp.setMacroProvider(createMacroProvider(file_tree));
		SVDBFile svdb_f = factory.parse(copier.copy(), file_tree.getFilePath(),
				markers);

		if (svdb_f.getFilePath() == null) {
			System.out.println("file path: " + path + " is null");
		}

		// propagateMarkersPreProc2DB(file_tree, svdb_pp, svdb_f);
		// addMarkers(path, svdb_f);

		return new Tuple<SVDBFile, SVDBFile>(svdb_pp, svdb_f);
		 */
		return null;
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	public synchronized SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	public synchronized SVDBFileTree findFileTree(
			String 		path,
			boolean 	is_argfile) {
		ensureIndexUpToDate(new NullProgressMonitor());
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path,
				is_argfile);

		return ft;
	}

	public void dispose() {
		fLog.debug("dispose() - " + getBaseLocation());
		if (fCache != null) {
			fCache.sync();
		}
		if (fFileSystemProvider != null) {
			fFileSystemProvider.dispose();
		}
	}

	/**
	 * getFileNames() -- implementation for IndexIterator
	 * @param monitor
	 * @return
	 */
	public Iterable<String> getFileNames(IProgressMonitor monitor) {
		return new Iterable<String>() {
			public Iterator<String> iterator() {
				List<String> ret = new ArrayList<String>();
				synchronized (fIndexCacheData) {
					ret.addAll(fIndexCacheData.fSrcFileList);
				}
				return ret.iterator();
			}
		};
	}

	/**
	 * Add the global declarations from the specified scope to the declaration
	 * cache
	 * 
	 * @param filename
	 * @param scope
	private void cacheDeclarations(SVDBFile file) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData
				.getDeclCacheMap();

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "cacheDeclarations: " + file.getFilePath());
		}

		if (!decl_cache.containsKey(file.getFilePath())) {
			decl_cache.put(file.getFilePath(),
					new ArrayList<SVDBDeclCacheItem>());
		} else {
			decl_cache.get(file.getFilePath()).clear();
		}

		Set<String> processed_files = new HashSet<String>();
		processed_files.add(file.getFilePath());

		cacheDeclarations(processed_files, file.getFilePath(),
				decl_cache.get(file.getFilePath()), null, null, file, false);

		SVDBFileTree ft = findFileTree(file.getFilePath(), false);
		if (ft != null) {
			cacheDeclarations(processed_files, file.getFilePath(),
					decl_cache.get(file.getFilePath()), null, null,
					ft.getSVDBFile(), true);
		}
	}
	 */

	/**
	 * Process the FileTree of a package to locate include files
	 */
	private void cachePkgDeclFileTree(ISVDBChildParent scope,
			List<SVDBDeclCacheItem> pkgitem_list, SVDBPackageDecl pkg) {
		int pkg_start = (pkg.getLocation() != null) ? pkg.getLocation()
				.getLine() : 0;
		int pkg_end = (pkg.getEndLocation() != null) ? pkg.getEndLocation()
				.getLine() : -1;
		Set<String> processed_files = new HashSet<String>();

		fLog.debug("--> cachePkgDeclFileTree: " + pkg.getName() + " "
				+ pkg_start + ".." + pkg_end);

		for (ISVDBChildItem item : scope.getChildren()) {
			int line = (item.getLocation() != null) ? (item.getLocation()
					.getLine()) : -1;
			if (fDebugEn) {
				fLog.debug("cachePkgDeclFileTree: process " + item.getType()
						+ " @ " + line + " (package bounds " + pkg_start + ".."
						+ pkg_end + ")");
			}

			if (item.getType().equals(SVDBItemType.Include)
					&& line >= pkg_start && line <= pkg_end) {
				// First, find the pre-processor file corresponding to this
				// include
				cachePkgDeclIncFile(processed_files, pkg.getName(),
						pkgitem_list, ((SVDBInclude) item).getName());

			} else if (item instanceof ISVDBChildParent) {
				// Search the sub-scope
				cachePkgDeclFileTree((ISVDBChildParent) item, pkgitem_list, pkg);
			}
		}
		fLog.debug("<-- cachePkgDeclFileTree: " + pkg.getName() + " "
				+ pkg_start + ".." + pkg_end);
	}

	private void cachePkgDeclIncFile(Set<String> processed_files,
			String pkgname, List<SVDBDeclCacheItem> pkgitem_list, String inc) {
		if (fDebugEn) {
			fLog.debug("Cache included file \"" + inc + "\"");
		}
		SVDBFile abs_pp_file = fCache.getPreProcFile(new NullProgressMonitor(),
				inc);

		if (abs_pp_file != null) {
			if (fDebugEn) {
				fLog.debug("File path is absolute");
			}

		} else {
			if (fDebugEn) {
				fLog.debug("Searching for relative path");
			}

			System.out.println("TODO: findIncludedFile");
		}

		if (abs_pp_file != null) {
			// Found something
			if (fDebugEn) {
				fLog.debug("Included file already parsed: "
						+ abs_pp_file.getFilePath());
			}

			SVDBFile file = fCache.getFile(new NullProgressMonitor(),
					abs_pp_file.getFilePath());
			if (file != null) {
				// Add the contents of the target file to the package
				fLog.debug("Calling cacheDeclarations: pkgname=" + pkgname);
				if (!processed_files.contains(file.getFilePath())) {
					processed_files.add(file.getFilePath());
					cacheDeclarations(processed_files, file.getFilePath(),
							null, pkgname, pkgitem_list, file, false);
					// Now, get the file tree and add sub-included files
					SVDBFileTree ft = fCache.getFileTree(
							new NullProgressMonitor(),
							abs_pp_file.getFilePath(), false);
					SVDBFile pp_file = ft.getSVDBFile();
					synchronized (pp_file) {
						for (ISVDBChildItem item : pp_file.getChildren()) {
							if (item.getType() == SVDBItemType.Include) {
								cachePkgDeclIncFile(processed_files, pkgname,
										pkgitem_list,
										((SVDBInclude) item).getName());
							}
						}
					}
				} else {
					if (fDebugEn) {
						fLog.debug("File " + file.getFilePath()
								+ " already processed");
					}
				}
			} else {
				// File probably hasn't been parsed yet
				fLog.debug("Deferring caching of file \""
						+ abs_pp_file.getFilePath() + "\"");
			}
		} else {
			fLog.debug("Failed to find include file \"" + inc + "\"");
		}
	}

	private void cacheDeclarations(
			Set<String> 			processed_files,
			String 					filename, 
			List<SVDBDeclCacheItem> decl_list, 
			String 					pkgname,
			List<SVDBDeclCacheItem> pkgitem_list, 
			ISVDBChildParent 		scope,
			boolean 				is_ft) {
		if (fDebugEn) {
			fLog.debug("--> cacheDeclarations(file=" + filename + ", pkg="
					+ pkgname + ", " + scope);
		}

		for (ISVDBChildItem item : scope.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + item.getType() + " "
						+ SVDBItem.getName(item));
			}
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				SVDBPackageDecl pkg = (SVDBPackageDecl) item;
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename, pkg
							.getName(), item.getType(), is_ft));
				}
				Map<String, List<SVDBDeclCacheItem>> pkg_map = fIndexCacheData
						.getPackageCacheMap();

				if (pkg_map.containsKey(pkg.getName())) {
					pkg_map.get(pkg.getName()).clear();
				} else {
					pkg_map.put(pkg.getName(),
							new ArrayList<SVDBDeclCacheItem>());
				}

				// Search the FileTree to find files included within the package
				if (!is_ft) {
					SVDBFileTree ft = fCache.getFileTree(
							new NullProgressMonitor(), filename, false);
					if (ft != null) {
						cachePkgDeclFileTree(ft.getSVDBFile(),
								pkg_map.get(pkg.getName()), pkg);
					} else {
						fLog.error("Failed to locate FileTree for \""
								+ filename + "\"");
					}
				}

				// Now, proceed looking for explicitly-included content
				cacheDeclarations(processed_files, filename, decl_list,
						pkg.getName(), pkg_map.get(pkg.getName()), pkg, false);
			} else if (item.getType().isElemOf(SVDBItemType.Function,
					SVDBItemType.Task, SVDBItemType.ClassDecl,
					SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl,
					SVDBItemType.ProgramDecl)) {
				fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
						+ ((ISVDBNamedItem) item).getName() + " to cache");
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							is_ft));
				}

				// Add the declarations to the package cache as well
				if (pkgname != null) {
					if (fDebugEn) {
						fLog.debug("Adding " + SVDBItem.getName(item)
								+ " to package cache \"" + pkgname + "\"");
					}
					pkgitem_list.add(new SVDBDeclCacheItem(this, filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							is_ft));
				} else {
					fLog.debug("pkgname is null");
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt decl = (SVDBVarDeclStmt) item;

				for (ISVDBChildItem ci : decl.getChildren()) {
					SVDBVarDeclItem di = (SVDBVarDeclItem) ci;
					fLog.debug(LEVEL_MID,
							"Adding var declaration: " + di.getName());

					if (decl_list != null) {
						decl_list.add(new SVDBDeclCacheItem(this, filename, di
								.getName(), SVDBItemType.VarDeclItem, is_ft));
					}
				}
			} else if (item.getType() == SVDBItemType.TypedefStmt) {
				// Add entries for the typedef
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							is_ft));
				}

				// Add the declarations to the package cache as well
				if (pkgname != null) {
					pkgitem_list.add(new SVDBDeclCacheItem(this, filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							is_ft));
				}

				SVDBTypedefStmt td = (SVDBTypedefStmt) item;
				if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					// Add entries for all enumerators
					SVDBTypeInfoEnum e = (SVDBTypeInfoEnum) td.getTypeInfo();
					fLog.debug("Adding enum " + e.getName() + " to cache");
					for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
						fLog.debug("Adding enumerator " + en.getName()
								+ " to cache");
						if (decl_list != null) {
							decl_list.add(new SVDBDeclCacheItem(this, filename,
									((ISVDBNamedItem) en).getName(), en
											.getType(), is_ft));
						}
						// Add the declarations to the package cache as well
						if (pkgname != null) {
							pkgitem_list.add(new SVDBDeclCacheItem(this,
									filename,
									((ISVDBNamedItem) item).getName(), item
											.getType(), is_ft));
						}
					}
				}
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				cacheDeclarations(processed_files, filename, decl_list,
						pkgname, pkgitem_list, (SVDBPreProcCond) item, is_ft);
			} else if (item.getType() == SVDBItemType.MacroDef) {
				if (decl_list != null) {
					fLog.debug(LEVEL_MID,
							"Add macro declaration \"" + SVDBItem.getName(item)
									+ "\"");
					decl_list.add(new SVDBDeclCacheItem(this, filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							is_ft));
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- cacheDeclarations(" + filename + ", " + pkgname
					+ ", " + scope);
		}
	}

	/*
	private void cacheReferences(SVDBFile file) {
		SVDBFileRefCollector collector = new SVDBFileRefCollector();
		collector.visitFile(file);

		Map<String, SVDBRefCacheEntry> ref_map = getCacheData()
				.getReferenceCacheMap();
		if (ref_map.containsKey(file.getFilePath())) {
			ref_map.remove(file.getFilePath());
		}
		SVDBRefCacheEntry ref = collector.getReferences();
		ref.setFilename(file.getFilePath());
		ref_map.put(file.getFilePath(), ref);
	}
	 */

	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> pkg_cache = fIndexCacheData
				.getPackageCacheMap();

		ensureIndexUpToDate(monitor);

		List<SVDBDeclCacheItem> pkg_content = pkg_cache.get(pkg_item.getName());

		if (pkg_content != null) {
			ret.addAll(pkg_content);
		}

		return ret;
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData
				.getDeclCacheMap();
		ensureIndexUpToDate(monitor);

		for (Entry<String, List<SVDBDeclCacheItem>> e : decl_cache.entrySet()) {
			for (SVDBDeclCacheItem item : e.getValue()) {
				if (matcher.match(item, name)) {
					ret.add(item);
				}
			}
		}

		return ret;
	}

	public List<SVDBRefCacheItem> findReferences(IProgressMonitor monitor,
			String name, ISVDBRefMatcher matcher) {
		List<SVDBRefCacheItem> ret = new ArrayList<SVDBRefCacheItem>();

		ensureIndexUpToDate(monitor);

		Map<String, SVDBRefCacheEntry> ref_cache = fIndexCacheData
				.getReferenceCacheMap();
		for (Entry<String, SVDBRefCacheEntry> e : ref_cache.entrySet()) {
			matcher.find_matches(ret, e.getValue(), name);
		}

		for (SVDBRefCacheItem item : ret) {
			item.setRefFinder(this);
		}

		return ret;
	}

	public List<SVDBRefItem> findReferences(
			IProgressMonitor 		monitor,
			SVDBRefCacheItem 		item) {
		ensureIndexUpToDate(monitor);

		SVDBRefFinder finder = new SVDBRefFinder(item.getRefType(),
				item.getRefName());

		SVDBFile file = findFile(item.getFilename());

		return finder.find_refs(file);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		ensureIndexUpToDate(monitor);

		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(item.getFilename(), false);
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			file = findFile(item.getFilename());
		}

		return file;
	}

	// FIXME:
	public SVDBFile getDeclFilePP(
			IProgressMonitor 		monitor,
			SVDBDeclCacheItem 		item) {
		ensureIndexUpToDate(monitor);

		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(item.getFilename(), false);
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			file = findFile(item.getFilename());
		}

		return file;
	}

	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}

	private void discoverRootFiles(IProgressMonitor monitor) {
		fLog.debug("discoverRootFiles - " + getBaseLocation());

		clearFilesList();
		clearIncludePaths();
		clearDefines();

		monitor.beginTask("Discover Root Files", 4);

		// Add an include path for the arg file location
		addIncludePath(getResolvedBaseLocationDir());

		String resolved_argfile_path = getResolvedBaseLocation();
		if (getFileSystemProvider().fileExists(resolved_argfile_path)) {
			processArgFile(new SubProgressMonitor(monitor, 4), null, null,
					getResolvedBaseLocation());
		} else {
			String msg = "Argument file \"" + getBaseLocation() + "\" (\""
					+ getResolvedBaseLocation() + "\") does not exist";
			fLog.error(msg);
			if (getProject() != null) {
				// TODO: must save this somewhere...
				getFileSystemProvider().addMarker(
						"${workspace_loc}/" + getProject(),
						ISVDBFileSystemProvider.MARKER_TYPE_ERROR, 0, msg);
			}
		}

		monitor.done();
	}

	private SVDBFile parseArgFile(
			String 				path, 
			Set<String> 		processed_paths,
			List<SVDBMarker> 	markers) {
		SVDBFile ret = new SVDBFile(path);
		InputStream in = null;

		String resolved_path = SVFileUtils.resolvePath(
				path, getResolvedBaseLocation(), fFileSystemProvider, true);

		if (processed_paths.contains(resolved_path)) {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error,
					MarkerKind.MissingInclude, "Recursive inclusion of file \""
							+ path + "\" (" + resolved_path + ")"));
		} else if ((in = getFileSystemProvider().openStream(resolved_path)) != null) {
			long last_modified = getFileSystemProvider().getLastModifiedTime(
					resolved_path);
			processed_paths.add(resolved_path);
			ISVArgFileVariableProvider vp = SVCorePlugin
					.getVariableProvider(getProjectHndl());
			SVArgFilePreProcessor pp = new SVArgFilePreProcessor(in,
					resolved_path, vp);

			SVArgFilePreProcOutput pp_out = pp.preprocess();

			SVArgFileLexer lexer = new SVArgFileLexer();
			lexer.init(null, pp_out);

			SVArgFileParser parser = new SVArgFileParser(
					SVFileUtils.getPathParent(getBaseLocation()),
					getResolvedBaseLocationDir(), getFileSystemProvider());
			parser.init(lexer, path);

			try {
				parser.parse(ret, markers);
			} catch (SVParseException e) {
			}

			processed_paths.add(resolved_path);

			if (fDebugEn) {
				fLog.debug("File: " + resolved_path + " has "
						+ markers.size() + " errors");
			}
			synchronized (getCache()) {
				getCache().setMarkers(resolved_path, markers, true);
				getCache().setFile(resolved_path, ret, true);
				getCache().setLastModified(resolved_path, last_modified, true);

			}
			if (fDebugEn) {
				fLog.debug("File(cached): " + resolved_path + " has "
						+ getCache().getMarkers(resolved_path).size()
						+ " errors");
			}
		} else {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error,
					MarkerKind.MissingInclude, "File \"" + path + "\" ("
							+ resolved_path + ") does not exist"));
		}

		return ret;
	}

	private void processArgFile(IProgressMonitor monitor, SVDBFileTree parent,
			Set<String> processed_paths, String path) {
		path = SVFileUtils.normalize(path);

		if (processed_paths == null) {
			processed_paths = new HashSet<String>();
		}
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		SVDBFileTree ft = new SVDBFileTree(path);
		SVDBFile argfile = parseArgFile(path, processed_paths, markers);

		if (parent != null) {
			ft.addIncludedByFile(parent.getFilePath());
			parent.addIncludedFile(path);
		}

		synchronized (getCache()) {
			getCache().setFile(path, argfile, true);
		}

		if (argfile != null) {

			for (ISVDBChildItem ci : argfile.getChildren()) {
				if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
					// Process the included file
					SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt) ci;
					String sub_path = SVFileUtils.resolvePath(stmt.getPath(),
							getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);

					// TODO: handle monitor
					if (getFileSystemProvider().fileExists(sub_path)) {
						if (!processed_paths.contains(sub_path)) {
							processArgFile(new NullProgressMonitor(), ft,
									processed_paths, sub_path);
						} else {
							SVDBMarker m = new SVDBMarker(MarkerType.Error,
									MarkerKind.MissingInclude,
									"Recursive inclusion of file \"" + path
											+ "\" (" + sub_path + ")");
							m.setLocation(stmt.getLocation());
							markers.add(m);
						}
					} else {
						/**
						 * SVDBMarker m = new SVDBMarker( MarkerType.Error,
						 * MarkerKind.MissingInclude, "Path \"" + sub_path +
						 * "\" does not exist");
						 * m.setLocation(stmt.getLocation()); markers.add(m);
						 */
					}
				} else if (ci.getType() == SVDBItemType.ArgFileIncDirStmt) {
					SVDBArgFileIncDirStmt stmt = (SVDBArgFileIncDirStmt) ci;
					addIncludePath(stmt.getIncludePath());
				} else if (ci.getType() == SVDBItemType.ArgFileDefineStmt) {
					SVDBArgFileDefineStmt stmt = (SVDBArgFileDefineStmt) ci;
					addDefine(stmt.getKey(), stmt.getValue());
				} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
					SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt) ci;
					String res_f = SVFileUtils.resolvePath(stmt.getPath(), 
							getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);

					if (getFileSystemProvider().fileExists(res_f)) {
						addFile(res_f, false);
					}
				} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
					SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt) ci;

					if (getFileSystemProvider().isDir(stmt.getSrcLibPath())) {
						List<String> paths = getFileSystemProvider().getFiles(
								stmt.getSrcLibPath());
						Set<String> exts = SVFScanner.getSrcExts();
						for (String file_p : paths) {
							int last_dot = file_p.lastIndexOf('.');
							if (last_dot != -1) {
								String ext = file_p.substring(last_dot);
								if (exts.contains(ext)) {
									addFile(file_p, false);
								}
							}
						}
					} else {
						SVDBMarker m = new SVDBMarker(MarkerType.Error,
								MarkerKind.MissingInclude,
								"Library Path directory \""
										+ stmt.getSrcLibPath()
										+ "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
					}
				}
			}

			// Save the markers, which might have been updated
			synchronized (getCache()) {
				getCache().setMarkers(path, markers, true);
				getCache().setFileTree(path, ft, true);
			}

			// Propagate markers to filesystem
			propagateMarkers(path);
		} else {
			// Problem with root argument file
			// TODO: propagate markers
		}

	}

	/**
	 * findIncFile()
	 * 
	 * Implementation of 
	 */
	public Tuple<String, InputStream> findIncFile(String incfile) {
		synchronized (fIndexCacheData) {
			for (String path : fIndexCacheData.fIncludePathList) {
				String fullpath = SVFileUtils.resolvePath(incfile, path, fFileSystemProvider, true);
				if (fFileSystemProvider.fileExists(fullpath)) {
					InputStream in = fFileSystemProvider.openStream(fullpath);
					return new Tuple<String, InputStream>(fullpath, in);
				}
			}
		}
	
		return null;
	}
	
	public int mapFilePathToId(String path, boolean add) {
		synchronized (fIndexCacheData) {
			int idx = (fIndexCacheData.fSrcFileList.indexOf(path)+1);
			
			if (idx < 1 && add) {
				idx = (fIndexCacheData.fSrcFileList.size()+1);
				fIndexCacheData.fSrcFileList.add(path);
			}
			
			return idx;
		}
	}
	
	public String mapFileIdToPath(int id) {
		synchronized (fIndexCacheData) {
			if (id > 0 && id <= fIndexCacheData.fSrcFileList.size()) {
				return fIndexCacheData.fSrcFileList.get(id);
			}
			
			return null;
		}
	}

	private void parseFile(String path) {
		long start, end;
		ParserSVDBFileFactory f = new ParserSVDBFileFactory();
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		InputStream in = fFileSystemProvider.openStream(path);

		start = System.currentTimeMillis();
		SVPreProcessor2 pp = new SVPreProcessor2(path, in, this, this);
		SVPreProcOutput pp_out = pp.preprocess(markers);
		end = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Pre-process " + path + ": " +
					(end-start) + "ms");
		}
		
		SVDBFileTree ft = pp_out.getFileTree();

		start = System.currentTimeMillis();
		SVDBFile file = f.parse(pp_out, path, markers);
		end = System.currentTimeMillis();

		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Parse " + path + ": " +
					(end-start) + "ms");
		}
	
		synchronized (fCache) {
			fCache.setFile(path, file, false);
			fCache.setFileTree(path, ft, false);
			fCache.setMarkers(path, markers, false);
		}
	}
	
	private void buildIndex(IProgressMonitor monitor) {
		long start_time, end_time;

		// First, parse the argument files
		start_time = System.currentTimeMillis();
		discoverRootFiles(new SubProgressMonitor(monitor, 100));
		end_time = System.currentTimeMillis();

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse argument files -- " + (end_time - start_time)
					+ "ms");
		}

		// Next, parse each of the discovered file paths
		List<String> paths = new ArrayList<String>();

		synchronized (fIndexCacheData) {
			paths.addAll(fIndexCacheData.fRootFileList);
		}

		start_time = System.currentTimeMillis();
		for (String path : paths) {
			fLog.debug("Path: " + path);
			if (fFileSystemProvider.fileExists(path)) {
				parseFile(path);
			}
		}
		end_time = System.currentTimeMillis();

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse source files -- " + (end_time - start_time)
					+ "ms");
		}
	}
}
