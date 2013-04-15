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

package net.sf.sveditor.core.db.index.argfile;

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
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexFactoryUtils;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRefresh;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
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
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex2 implements 
		ISVDBIndex, ISVDBIndexInt, ISVDBRefFinder, 
		ILogLevelListener, ILogLevel {

	public String 								fProjectName;
	private IProject 							fProject;
	private String 								fBaseLocation;
	private String 								fResolvedBaseLocation;
	private String 								fBaseLocationDir;
	
	private SVDBArgFileIndexBuildData			fBuildData;

	private boolean 							fCacheDataValid;

	private List<ISVDBIndexChangeListener> 		fIndexChangeListeners;

	private LogHandle fLog;
	private ISVDBFileSystemProvider 			fFileSystemProvider;

	private SVDBIndexConfig 					fConfig;

	private boolean 							fDebugEn;

	private boolean 							fInWorkspaceOk;

	/**
	 * True if the root file list is valid.
	 */
	private boolean								fIndexValid;
	private boolean 							fAutoRebuildEn;
	private boolean 							fIsDirty;
	
	private ISVDBIndexBuilder					fIndexBuilder;
	
	
	private SVDBArgFileIndex2(String project) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex2");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fAutoRebuildEn = true;

		// Try to obtain the project handle
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			fProject = root.getProject(fProjectName);
		} catch (IllegalStateException e) {
			// Occurs if the workspace is closed
		}
	}

	public SVDBArgFileIndex2(
			String 						project, 
			String 						base_location,
			ISVDBFileSystemProvider 	fs_provider, 
			ISVDBIndexCache 			cache,
			SVDBIndexConfig 			config) {
		this(project);
		fBaseLocation = base_location;
		fBuildData = new SVDBArgFileIndexBuildData(cache, base_location);
		/** TODO:
		fCache = cache;
		fCacheMgr = fCache.getCacheMgr();
		 */
		fConfig = config;

		setFileSystemProvider(fs_provider);
		fInWorkspaceOk = (base_location.startsWith("${workspace_loc}"));
		fAutoRebuildEn = true;
	}
	
	public void setIndexBuilder(ISVDBIndexBuilder builder) {
		fIndexBuilder = builder;
	}

	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		SVDBIndexChangePlan plan = new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
		
		if (changes == null || !fIndexValid) {
			if (!fIndexValid) {
				// Return a 'build me' plan, since we're not valid
				plan = new SVDBIndexChangePlanRebuild(this);
			}
		} else {
			synchronized (fBuildData) {
				for (SVDBIndexResourceChangeEvent ev : changes) {
					System.out.println("Event: " + ev.getPath());
					if (fBuildData.fIndexCacheData.fSrcFileList.contains(ev.getPath())) {
						System.out.println("  Create Rebuild plan");
						plan = new SVDBIndexChangePlanRebuild(this);
						break;
					} else if (fBuildData.fIndexCacheData.fArgFilePaths.contains(ev.getPath())) {
						System.out.println("  Create Rebuild plan");
						plan = new SVDBIndexChangePlanRebuild(this);
						break;
					}
				}
			}
		}
		
		return plan;
	}

	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		System.out.println("execIndexChangePlan: " + plan.getType());
		
		switch (plan.getType()) {
			case Refresh: {
				refresh_index(monitor);
			} break;
			
			case RebuildIndex: {
				rebuild_index(monitor);
			} break;
			
			default: {
				
			} break;
		}
		
		monitor.done();
	}

	@SuppressWarnings("unchecked")
	private void refresh_index(IProgressMonitor monitor) {
		monitor.beginTask("Initialize index " + getBaseLocation(), 100);

		// Initialize the cache
		IProgressMonitor m = new SubProgressMonitor(monitor, 1);

		if (fCacheDataValid) {
			fCacheDataValid = checkCacheValid();
		} else {
			System.out.println("Cache " + getBaseLocation() + " is invalid on entry");
		}

		if (fCacheDataValid) {
			if (fDebugEn) {
				fLog.debug("Cache is valid");
			}
			System.out.println("Cache is valid");
			fIndexValid = true;

			// If we've determined the index data is valid, then we need to
			// fixup some index entries
			if (fBuildData.fIndexCacheData.getDeclCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : fBuildData.getDeclCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also update the package cache
			if (fBuildData.fIndexCacheData.getPackageCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : 
						fBuildData.fIndexCacheData.getPackageCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also re-set filenames on the reference cache
			if (fBuildData.fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : 
					fBuildData.fIndexCacheData.getReferenceCacheMap().entrySet()) {
					e.getValue().setFilename(e.getKey());
				}
			}

			// Register all files with the directory set
			for (String f : fBuildData.fCache.getFileList(false)) {
				addFileDir(fBuildData, f);
			}
		} else {
			System.out.println("Cache " + getBaseLocation() + " is invalid");
			if (fDebugEn) {
				fLog.debug("Cache " + getBaseLocation() + " is invalid");
			}
			invalidateIndex(m, "Cache is invalid", true);
		}
		// set the version to check later
		fBuildData.fIndexCacheData.setVersion(SVCorePlugin.getVersion());

		// Set the global settings anyway
		if (fConfig != null
				&& fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
			Map<String, String> define_map = (Map<String, String>) fConfig
					.get(ISVDBIndexFactory.KEY_GlobalDefineMap);

			fBuildData.fIndexCacheData.clearGlobalDefines();
			for (String key : define_map.keySet()) {
				fBuildData.fIndexCacheData.setGlobalDefine(key, define_map.get(key));
			}
		}		
	}
	
	private void rebuild_index(IProgressMonitor	monitor) {
		ISVDBIndexCache new_cache = 
				fBuildData.fCacheMgr.createIndexCache(getProject(), getBaseLocation());
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(
				new_cache, getBaseLocation());
		
		synchronized (fBuildData) {
			// Copy in relevant information
			build_data.getGlobalDefines().putAll(fBuildData.getGlobalDefines());
			build_data.fFileSystemProvider = fFileSystemProvider;
		}
	
		monitor.beginTask("Rebuild " + getBaseLocation(), 10000);

		// Invalidate Index
//		fIndexValid = false;
//		fIndexCacheData.clear();
//		synchronized (fCache) {
//			fCache.clear(new SubProgressMonitor(monitor, 250));
//		}
//		fMissingIncludes.clear();

		// Rebuild the index
		buildIndex(new SubProgressMonitor(monitor, 9750), build_data);
		
		// TODO: Apply new 
	
//		synchronized (fCache) {
//			fCache.sync();
//		}
	
//		fIndexValid = true;
		
		// Apply the newly-built result
		synchronized (fBuildData) {
			fBuildData.apply(build_data);
		}
		
		// Notify clients that the index has new data
		synchronized (fIndexChangeListeners) {
			for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
				l.index_rebuilt();
			}
		}
	
		monitor.done();
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
			fLog.debug("Cached version=" + fBuildData.fIndexCacheData.getVersion()
					+ " version=" + version);
		}

		if (fBuildData.fIndexCacheData.getVersion() == null
				|| !fBuildData.fIndexCacheData.getVersion().equals(version)) {
			valid = false;
			return valid;
		}

		// Confirm that global defines are the same
		if (fConfig != null) {
			// First check to see if all configured global defines are present
			if (fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = (Map<String, String>) fConfig
						.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				if (define_map.size() != fBuildData.getGlobalDefines()
						.size()) {
					if (fDebugEn) {
						fLog.debug(LEVEL_MID,
								"Cache invalid -- size of global defines is different");
					}
					valid = false;
				} else {
					// Check all defines
					for (Entry<String, String> e : define_map.entrySet()) {
						if (fBuildData.getGlobalDefines().containsKey(
								e.getKey())) {
							if (!fBuildData.getGlobalDefines()
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
			} else if (fBuildData.getGlobalDefines().size() > 0) {
				// Local index has defines and the incoming config does not
				if (fDebugEn) {
					fLog.debug(LEVEL_MID,
							"Cache invalid -- no global defines, and cache has");
				}
				valid = false;
			}
		}

		if (fBuildData.fCache.getFileList(false).size() > 0) {
			for (String path : fBuildData.fCache.getFileList(false)) {
				long fs_timestamp = fFileSystemProvider.getLastModifiedTime(path);
				long cache_timestamp = fBuildData.fCache.getLastModified(path);
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
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		SubProgressMonitor m;
		
		fIndexBuilder = builder;

		fBuildData.fIndexCacheData = new SVDBArgFileIndexCacheData(getBaseLocation());
		fCacheDataValid = fBuildData.fCache.init(new NullProgressMonitor(), 
				fBuildData.fIndexCacheData, fBaseLocation);
		/** TODO: 
		 */
		
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRefresh plan = new SVDBIndexChangePlanRefresh(this);
			System.out.println("Launch refresh: " + getBaseLocation());
			fIndexBuilder.build(plan);
		} else {
			// run the refresh in-line
			refresh_index(monitor);
		}



		monitor.done();
	}

	/**
	 * 
	 */
	public void loadIndex(IProgressMonitor monitor) {

		if (!fIndexValid) {
			if (fIndexBuilder != null) {
				SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
				System.out.println("loadIndex build: " + getBaseLocation());
				SVDBIndexBuildJob job = fIndexBuilder.build(plan);

				job.waitComplete();
			} else {
				rebuild_index(monitor);
			}
			fIndexValid = true;
		}
	
		/*
		invalidateIndex(monitor, "loadIndex", true);
		
		buildIndex(monitor);

		synchronized (fCache) {
			fCache.sync();
		}
		
		fIndexValid = true;	
		 */
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
			SVDBIndexBuildJob build_job = null;
			
			if (fIndexBuilder != null) {
				// See if there is an active job 
				build_job = fIndexBuilder.findJob(this);
				
				if (build_job != null) {
					build_job.waitComplete();
				}
				
				if (!fIndexValid) {
					// Schedule a job
					SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
					System.out.println("ensureIndexUpToDate Build: " + getBaseLocation());
					build_job = fIndexBuilder.build(plan);
					build_job.waitComplete();
				}
				fIndexValid = true;
			} else {
				System.out.println("[ERROR] no builder and invalid");
			}
			
//			fLoadIndexJob.load();
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

		/** TODO:
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
		 */
	}

	public void rebuildIndex(IProgressMonitor monitor) {
		try {
			throw new Exception();
		} catch (Exception e) {
			System.out.println("rebuildIndex Request:");
			e.printStackTrace();
		}
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
			System.out.println("rebuildIndex Build: " + getBaseLocation());
			fIndexBuilder.build(plan);
		} else {
			invalidateIndex(monitor, "Rebuild Index Requested", true);
		}
	}

	public ISVDBIndexCache getCache() {
		return fBuildData.fCache;
	}

	public SVDBIndexConfig getConfig() {
		return fConfig;
	}

	private SVDBBaseIndexCacheData getCacheData() {
		return fBuildData.fIndexCacheData;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
		fBuildData.fFileSystemProvider = fs_provider;

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
		fBuildData.fIndexCacheData.setGlobalDefine(key, val);

		// Rebuild the index when something changes
		/** TODO:
		if (!fIndexCacheData.getGlobalDefines().containsKey(key)
				|| !fIndexCacheData.getGlobalDefines().get(key).equals(val)) {
			rebuildIndex(new NullProgressMonitor());
		}
		 */
	}

	public void clearGlobalDefines() {
		fBuildData.fIndexCacheData.clearGlobalDefines();
		/** TODO: should queue for rebuild?
		 */
	}

	/**
	 * getFileList() -- returns a list of all source files
	 */
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		ensureIndexUpToDate(monitor);
		
		List<String> ret = new ArrayList<String>();
		synchronized (fBuildData) {
			ret.addAll(fBuildData.fIndexCacheData.fSrcFileList);
		}
		
		return ret;
	}

	/**
	 * Implementation of ISVDBIndexIterator findFile()
	 */
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		String r_path = path;
		SVDBFile ret = null;
		if (fDebugEn) {
			fLog.debug("--> findFile: " + path);
		}
		ensureIndexUpToDate(monitor);

		// TODO: 
		synchronized (fBuildData) {
			ret = fBuildData.fCache.getFile(new NullProgressMonitor(), r_path);
		}
		
		if (ret == null) {
			ret = findFileInt(r_path);
		}
		
		monitor.done();

		if (fDebugEn) {
			fLog.debug("<-- findFile: " + path + " ret=" + ret);
		}

		return ret;
	}

	/**
	 * Method performs the core work of locating the contents 
	 * of a file. 
	 * 
	 * Preconditions:
	 * - Index up-to-date
	 * - Only resolved paths passed in
	 * @param r_path
	 * @return
	 */
	private SVDBFile findFileInt(String r_path) {
		SVDBFile ret = null;
		SVDBFile root_file = findRootFile(r_path);
		
		if (root_file != null) {
			// Copy 
			int file_id = fBuildData.mapFilePathToId(r_path, false);
			ret = new SVDBFile(r_path);
		
			synchronized (fBuildData) {
				extractFileContents(ret, root_file, file_id);
			}
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
		
		synchronized (fBuildData) {
			// Search the file tree of each root file
			for (String root_path : fBuildData.fCache.getFileList(false)) {
				SVDBFileTree ft = fBuildData.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if (findTargetFileTree(ft, paths) != null) {
					ret = fBuildData.fCache.getFile(new NullProgressMonitor(), root_path);
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
		
		synchronized (fBuildData) {
			// Search the file tree of each root file
			Set<String> file_list = fBuildData.fCache.getFileList(false);
//			System.out.println("file_list: " + file_list.size());
			for (String root_path : file_list) {
				SVDBFileTree ft = fBuildData.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
//				System.out.println("Check: " + root_path + " " + ft + " " + paths);
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
		
		SVDBLocation l = parent.getLocation();
		
		if (fDebugEn) {
			fLog.debug("--> extractFileContents " + SVDBItem.getName(parent) + 
					" l.file_id=" + ((l != null)?l.getFileId():"null") + " " + file_id);
		}
	
		if (l != null && l.getFileId() == file_id) {
			ret.addChildItem(parent);
			found_file = true;
			if (fDebugEn) {
				fLog.debug("  -- foundFile(parent) ; add " + SVDBItem.getName(parent));
			}
		} else {
			for (ISVDBChildItem c : parent.getChildren()) {
				l = c.getLocation();
				if (l != null && l.getFileId() == file_id) {
					ret.addChildItem(c);
					found_file = true;
					if (fDebugEn) {
						fLog.debug("  -- foundFile ; add " + SVDBItem.getName(c));
					}
				} else if (c instanceof ISVDBChildParent) {
					if (!found_file) {
						extractFileContents(ret, (ISVDBChildParent)c, file_id);
					} else {
						break;
					}
				}
			}
		}
		
		if (fDebugEn) {
			fLog.debug("<-- extractFileContents " + SVDBItem.getName(parent));
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
	
	@SuppressWarnings("unused")
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
		
		synchronized (fBuildData) {
			root_path_l.addAll(fBuildData.fCache.getFileList(false));
		}

		for (String root_path : root_path_l) {
			SVDBFileTree ft = fBuildData.fCache.getFileTree(
					new NullProgressMonitor(), root_path, false);

			if (findTargetFileTree(ft, paths) != null) {
				ret = ft;
				break;
			}
		}
	
		return ret;
	}
	
	@SuppressWarnings("unused")
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

		SVDBFileTree ft = findTargetFileTree(r_path);
	
		if (ft != null) {
			file = ft.fSVDBFile;
		}

		return file;
	}

	public List<SVDBMarker> getMarkers(String path) {
		if (fDebugEn) {
			fLog.debug("-> getMarkers: " + path);
		}
		
		// TODO: Update implementation
		/* SVDBFile file = */findFile(path);

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		// TODO: Doesn't consider that root file isn't necessarily what we're after
		boolean is_argfile = false;
		String r_path = path;
	
		synchronized (fBuildData) {
			is_argfile = fBuildData.fIndexCacheData.fArgFilePaths.contains(path);
		}
		
		if (is_argfile) {
			synchronized (fBuildData) {
//				SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), r_path, true);
//						ft.fMarkers);
				markers.addAll(fBuildData.fCache.getMarkers(r_path));
			}
		} else {
			findFileMarkersInt(markers, path);
		}
			
		if (fDebugEn) {
			fLog.debug("<- getMarkers: " + path + ": " + markers.size());
		}

		return markers;
	}

	/**
	 * Locates markers for the specified file and adds them to the list
	 * 
	 * @param markers
	 * @param r_path
	 */
	private void findFileMarkersInt(List<SVDBMarker> markers, String r_path) {
		List<SVDBMarker>	root_markers = null;
		int 				file_id = -1;
		SVDBFileTree 		target_ft = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(r_path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			/*
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
			 */
		}
		
		synchronized (fBuildData) {
			// Search the file tree of each root file
			for (String root_path : fBuildData.fCache.getFileList(false)) {
				SVDBFileTree ft = fBuildData.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if ((target_ft = findTargetFileTree(ft, paths)) != null) {
					file_id = fBuildData.mapFilePathToId(root_path, false);
					root_markers = fBuildData.fCache.getMarkers(root_path);
					break;
				}
			}
			
			if (root_markers != null) {
				for (SVDBMarker m : root_markers) {
					if (m.getLocation() != null && m.getLocation().getFileId() == file_id) {
						markers.add(m);
					}
				}
			}
		
			if (target_ft != null && target_ft.fMarkers != null) {
				for (SVDBMarker m : target_ft.fMarkers) {
					markers.add(m);
				}
			}
		}
	}

	private void addFile(
			SVDBArgFileIndexBuildData 	build_data, 
			String 						path, 
			boolean 					is_argfile) {
		fLog.debug("addFile: " + path + " is_argfile=" + is_argfile);
		long last_modified = build_data.fFileSystemProvider.getLastModifiedTime(path);
		build_data.fCache.addFile(path, is_argfile);
		build_data.fCache.setLastModified(path, last_modified, is_argfile);
		
		if (!is_argfile) {
			build_data.fIndexCacheData.fRootFileList.add(path);
		}

		addFileDir(build_data, path);
	}

	private void addFileDir(SVDBArgFileIndexBuildData build_data, String file_path) {
		File f = new File(file_path);
		File p = f.getParentFile();

		if (p != null && !build_data.fFileDirs.contains(p.getPath())) {
			build_data.fFileDirs.add(p.getPath());
		}
	}

	/** Obsolete?
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
	 */

	// TODO: This should probably be handled externally
	private void propagateMarkers(String path) {
		List<SVDBMarker> ml = fBuildData.fCache.getMarkers(path);
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
		
		for (String inc_dir : fBuildData.fIndexCacheData.getIncludePaths()) {
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

	public Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor 	monitor,
			InputStream 		in, 
			String 				path, 
			List<SVDBMarker> 	markers) {
		String r_path = SVFileUtils.resolvePath(
				path, getResolvedBaseLocation(), 
				fFileSystemProvider, fInWorkspaceOk);
		
		if (!fFileSystemProvider.fileExists(r_path)) {
			fLog.debug("parse: path " + r_path + " does not exist");
			return null;
		}

		// TODO: should we update the index, or keep passive?
		
		// First, ensure index is up-to-date
		ensureIndexUpToDate(monitor);
		
		SVDBFileTree ft = findTargetFileTree(r_path);
	
		//
		// TODO: using 'this' as the include provider 
		// may not be ideal
		SVPreProcessor2 preproc = new SVPreProcessor2(
				r_path, in, fBuildData, fReadOnlyFileMapper);
		
		// TODO: add macros from FT
		if (ft != null) {
			fLog.debug("parse: failed to find target filetree for " + r_path);
//			return null;
		}
		
		fLog.debug("--> PreProcess " + r_path);
		SVPreProcOutput out = preproc.preprocess();
		fLog.debug("<-- PreProcess " + r_path);
		
		ParserSVDBFileFactory f = new ParserSVDBFileFactory();
		f.setFileMapper(fReadOnlyFileMapper);

		fLog.debug("--> Parse " + r_path);
		SVDBFile file = f.parse(out, r_path, markers);
		fLog.debug("<-- Parse " + r_path);
		SVDBFile file_ft = null;
		
		// TODO: collect markers from FT 
		
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
		return new Tuple<SVDBFile, SVDBFile>(file_ft, file);
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	public SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	public synchronized SVDBFileTree findFileTree(
			String 		path,
			boolean 	is_argfile) {
		ensureIndexUpToDate(new NullProgressMonitor());
		SVDBFileTree ft = fBuildData.fCache.getFileTree(
				new NullProgressMonitor(), path, is_argfile);

		return ft;
	}

	public void dispose() {
		fLog.debug("dispose() - " + getBaseLocation());
		if (fBuildData.fCache != null) {
			fBuildData.fCache.sync();
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
				synchronized (fBuildData) {
					ret.addAll(fBuildData.fIndexCacheData.fSrcFileList);
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
	 */
	private void cacheDeclarations(
			SVDBArgFileIndexBuildData	build_data,
			SVDBFile 					file, 
			SVDBFileTree 				ft) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = build_data.getDeclCacheMap();
		String file_path = ft.getFilePath();

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "cacheDeclarations: " + ft.getFilePath());
		}
		
		List<SVDBDeclCacheItem> file_item_list;
		
		if (!decl_cache.containsKey(file_path)) {
			file_item_list = new ArrayList<SVDBDeclCacheItem>();
			decl_cache.put(file_path, file_item_list);
		} else {
			file_item_list = decl_cache.get(file_path);
			file_item_list.clear();
		}

		Set<String> processed_files = new HashSet<String>();
		processed_files.add(file_path);
		
		int fileid = build_data.mapFilePathToId(file_path, false);

		cacheFileDeclarations(
				build_data,
				fileid, 
				file_item_list, 
				null, // pkg_item_list
				file,
				ft);
		/*
		cacheFileTreeDeclarations(
				ft,
				file_item_list);
		 */
				

		/** TODO: 
		SVDBFileTree ft = findFileTree(file.getFilePath(), false);
		if (ft != null) {
			cacheDeclarations(processed_files, file.getFilePath(),
					decl_cache.get(file.getFilePath()), null, null,
					ft.getSVDBFile(), true);
		}
		 */
	}

	/**
	 * Process the FileTree of a package to locate include files
	 */
	/** TODO:
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
	 */

	/** TODO:
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
	 */
	
	private void cacheFileDeclarations(
			SVDBArgFileIndexBuildData		build_data,
			int								fileid,
			List<SVDBDeclCacheItem> 		decl_list,
			List<SVDBDeclCacheItem> 		pkg_decl_list,
			ISVDBChildParent 				scope,
			SVDBFileTree					ft) {
		int curr_fileid = fileid;
		String curr_filename = build_data.mapFileIdToPath(curr_fileid);
		
		if (fDebugEn) {
			fLog.debug("--> cacheFileDeclarations(file=" + curr_filename + ", " + scope);
		}

		for (ISVDBChildItem item : scope.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + item.getType() + " "
						+ SVDBItem.getName(item));
			}
			
			if (item.getLocation() != null && 
					item.getLocation().getFileId() != curr_fileid &&
					item.getLocation().getFileId() > 0) {
				curr_fileid = item.getLocation().getFileId();
				curr_filename = build_data.mapFileIdToPath(curr_fileid);
			}
			
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				SVDBPackageDecl pkg = (SVDBPackageDecl) item;
				List<SVDBDeclCacheItem> pkg_decl_l;

				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename, pkg
							.getName(), item.getType(), false));
				}
				
				Map<String, List<SVDBDeclCacheItem>> pkg_map = 
						build_data.fIndexCacheData.getPackageCacheMap();

				if (pkg_map.containsKey(pkg.getName())) {
					pkg_decl_l = pkg_map.get(pkg.getName());
				} else {
					pkg_decl_l = new ArrayList<SVDBDeclCacheItem>();
					pkg_map.put(pkg.getName(), pkg_decl_l);
				}
				pkg_decl_l.clear();
				
				cacheFileDeclarations(build_data, curr_fileid, 
						decl_list, pkg_decl_l, pkg, ft);
				
				/* TODO: 
				SVDBPackageDecl pkg = (SVDBPackageDecl) item;

				// Now, proceed looking for explicitly-included content
				cacheDeclarations(processed_files, filename, decl_list,
						pkg.getName(), pkg_map.get(pkg.getName()), pkg, false);
				*/
			} else if (item.getType().isElemOf(SVDBItemType.Function,
					SVDBItemType.Task, SVDBItemType.ClassDecl,
					SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl,
					SVDBItemType.ProgramDecl)) {
				if (decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to cache");
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
				if (pkg_decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to pkg_decl cache");
					pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt decl = (SVDBVarDeclStmt) item;

				for (ISVDBChildItem ci : decl.getChildren()) {
					SVDBVarDeclItem di = (SVDBVarDeclItem) ci;
					fLog.debug(LEVEL_MID,
							"Adding var declaration: " + di.getName());

					if (decl_list != null) {
						decl_list.add(new SVDBDeclCacheItem(this, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
					if (pkg_decl_list != null) {
						pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
				}
			} else if (item.getType() == SVDBItemType.TypedefStmt) {
				// Add entries for the typedef
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(), false));
				}
				
				if (pkg_decl_list != null) {
					pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(), false));
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
							decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
									((ISVDBNamedItem) en).getName(), 
									en.getType(), false));
						}
						if (pkg_decl_list != null) {
							pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
									((ISVDBNamedItem) en).getName(), 
									en.getType(), false));
						}
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- cacheFileDeclarations(" + curr_filename + ", " + scope);
		}
	}
	
	@SuppressWarnings("unused")
	private void cacheFileTreeDeclarations(
			SVDBFileTree				ft,
			List<SVDBDeclCacheItem>		file_item_list) {
		
		SVDBFile file = ft.getSVDBFile();
		
		for (ISVDBChildItem c : file.getChildren()) {
			
			
		}
		
		for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
			cacheFileTreeDeclarations(ft_s, file_item_list);
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
		Map<String, List<SVDBDeclCacheItem>> pkg_cache = 
				fBuildData.fIndexCacheData.getPackageCacheMap();

		ensureIndexUpToDate(monitor);

		List<SVDBDeclCacheItem> pkg_content = pkg_cache.get(pkg_item.getName());

		if (pkg_content != null) {
			ret.addAll(pkg_content);
		}

		return ret;
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name, 
			ISVDBFindNameMatcher 	matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		ensureIndexUpToDate(monitor);
		
		Map<String, List<SVDBDeclCacheItem>> decl_cache = 
				fBuildData.fIndexCacheData.getDeclCacheMap();

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

		Map<String, SVDBRefCacheEntry> ref_cache = 
				fBuildData.fIndexCacheData.getReferenceCacheMap();
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

	private void discoverRootFiles(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData	build_data) {
		fLog.debug("discoverRootFiles - " + getBaseLocation());

		/*
		clearFilesList();
		clearIncludePaths();
		clearDefines();
		 */

		monitor.beginTask("Discover Root Files", 4);

		// Add an include path for the arg file location
		build_data.addIncludePath(getResolvedBaseLocationDir());

		String resolved_argfile_path = getResolvedBaseLocation();
		if (getFileSystemProvider().fileExists(resolved_argfile_path)) {
			processArgFile(
					new SubProgressMonitor(monitor, 4), 
					build_data,
					null, 
					null, 
					getResolvedBaseLocationDir(),
					getResolvedBaseLocation(), 
					false);
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
			SVDBArgFileIndexBuildData	build_data,
			String						path,
			String						base_location_dir,
			Set<String>					processed_paths,
			List<SVDBMarker>			markers) {
		SVDBFile ret = new SVDBFile(path);
		InputStream in = null;
		
		String resolved_path = SVFileUtils.resolvePath(
				path, base_location_dir, getFileSystemProvider(), true);
	
		if (processed_paths.contains(resolved_path)) {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"Recursive inclusion of file \"" + path + "\" (" + resolved_path + ")"));
		} else if ((in = getFileSystemProvider().openStream(resolved_path)) != null) {
			long last_modified = getFileSystemProvider().getLastModifiedTime(resolved_path);
			processed_paths.add(resolved_path);
			ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(getProjectHndl());
			SVArgFilePreProcessor pp = new SVArgFilePreProcessor(
					in, resolved_path, vp);
			
			SVArgFilePreProcOutput pp_out = pp.preprocess();
			
			SVArgFileLexer lexer = new SVArgFileLexer();
			lexer.init(null, pp_out);
			
			SVArgFileParser parser = new SVArgFileParser(
					base_location_dir, base_location_dir,
					getFileSystemProvider());
			/*
			SVArgFileParser parser = new SVArgFileParser(
					SVFileUtils.getPathParent(getBaseLocation()),
					getResolvedBaseLocationDir(),
					getFileSystemProvider());
			 */
			parser.init(lexer, path);
		
			try {
				parser.parse(ret, markers);
			} catch (SVParseException e) {}

			
			processed_paths.add(resolved_path);
			
			if (fDebugEn) {
				fLog.debug("File: " + resolved_path + " has " + markers.size() + " errors");
				for (SVDBMarker m : markers) {
					fLog.debug("  " + m.getMessage());
				}
			}
			build_data.fCache.setMarkers(resolved_path, markers, true);
			build_data.fCache.setFile(resolved_path, ret, true);
			build_data.fCache.setLastModified(resolved_path, last_modified, true);

			if (fDebugEn) {
				fLog.debug("File(cached): " + resolved_path + " has " + 
						build_data.fCache.getMarkers(resolved_path).size() + " errors");
			}
		} else {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"File \"" + path + "\" (" + resolved_path + ") does not exist"));
		}

		return ret;
	}	

	private void processArgFile(
			IProgressMonitor				monitor, 
			SVDBArgFileIndexBuildData		build_data,
			SVDBFileTree					parent,
			Set<String> 					processed_paths, 
			String							base_location_dir,
			String 							path,
			boolean							is_root) {
		path = SVFileUtils.normalize(path);

		if (processed_paths == null) {
			processed_paths = new HashSet<String>();
		}
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBFileTree ft = new SVDBFileTree(path);
		ft.setIncludeRoot((is_root || parent == null));
		
		String sub_base_location_dir = base_location_dir;
		
		if (is_root) {
			sub_base_location_dir = SVFileUtils.getPathParent(path);
		}
		
		// parse the argument file 
		SVDBFile argfile = parseArgFile(build_data, path, 
				sub_base_location_dir, processed_paths, markers);
		
		if (parent != null) {
			ft.addIncludedByFile(parent.getFilePath());
			parent.addIncludedFile(path);
		}

		build_data.fCache.setFile(path, argfile, true);
	
		build_data.addArgFilePath(path);
		
		if (argfile != null) {
			build_data.addArgFile(argfile);

			for (ISVDBChildItem ci : argfile.getChildren()) {
				if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
					// Process the included file
					SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
					String sub_path = SVFileUtils.resolvePath(stmt.getPath(), sub_base_location_dir, fFileSystemProvider, fInWorkspaceOk);
					
					// TODO: handle monitor
					if (getFileSystemProvider().fileExists(sub_path)) {
						if (!processed_paths.contains(sub_path)) {
							processArgFile(new NullProgressMonitor(), build_data,
									ft, processed_paths, sub_base_location_dir, 
									sub_path, stmt.isRootInclude());
						} else {
							SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
									"Recursive inclusion of file \"" + path + "\" (" + sub_path + ")");
							m.setLocation(stmt.getLocation());
							markers.add(m);
						}
					} else {
						/** 
						SVDBMarker m = new SVDBMarker(
								MarkerType.Error, MarkerKind.MissingInclude, 
								"Path \"" + sub_path + "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
						 */
					}
				} else if (ci.getType() == SVDBItemType.ArgFileIncDirStmt) {
					SVDBArgFileIncDirStmt stmt = (SVDBArgFileIncDirStmt)ci;
					build_data.addIncludePath(stmt.getIncludePath());
				} else if (ci.getType() == SVDBItemType.ArgFileDefineStmt) {
					SVDBArgFileDefineStmt stmt = (SVDBArgFileDefineStmt)ci;
					build_data.addDefine(stmt.getKey(), stmt.getValue());
				} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
					SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
					String res_f = SVFileUtils.resolvePath(stmt.getPath(), sub_base_location_dir, fFileSystemProvider, fInWorkspaceOk);

					if (getFileSystemProvider().fileExists(res_f)) {
						addFile(build_data, res_f, false);
					}
				} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
					SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt)ci;
					
					if (getFileSystemProvider().isDir(stmt.getSrcLibPath())) {
						List<String> paths = getFileSystemProvider().getFiles(stmt.getSrcLibPath());
						Set<String> exts = SVFScanner.getSrcExts();
						for (String file_p : paths) {
							int last_dot = file_p.lastIndexOf('.');
							if (last_dot != -1) {
								String ext = file_p.substring(last_dot);
								if (exts.contains(ext)) {
									addFile(build_data, file_p, false);
								}
							}
						}
					} else {
						SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
								"Library Path directory \"" + stmt.getSrcLibPath() + "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
					}
				}
			}

			// Save the markers, which might have been updated
			build_data.fCache.setMarkers(path, markers, true);
			build_data.fCache.setFileTree(path, ft, true);

			// Propagate markers to filesystem
// TODO:			propagateMarkers(path);
		} else {
			// Problem with root argument file
			// TODO: propagate markers
		}
	}
	
	
	private void parseFile(String path, SVDBArgFileIndexBuildData build_data) {
		long start, end;
		ParserSVDBFileFactory f = new ParserSVDBFileFactory();
		f.setFileMapper(build_data);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		InputStream in = fFileSystemProvider.openStream(path);

		start = System.currentTimeMillis();
		
		// Propagate defines to the pre-processor
		SVPreProcessor2 pp = new SVPreProcessor2(path, in, build_data, build_data);
		

		for (Entry<String, String> e : build_data.getGlobalDefines().entrySet()) {
			String key = e.getKey();
			String val = (e.getValue() != null)?e.getValue():"";
			pp.setMacro(key, val);
		}

		for (Entry<String, String> e : build_data.getDefines().entrySet()) {
			String key = e.getKey();
			String val = (e.getValue() != null)?e.getValue():"";
			pp.setMacro(key, val);
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> PreProcess " + path);
		}
		SVPreProcOutput pp_out = pp.preprocess();
		end = System.currentTimeMillis();
		
//		System.out.println("Pre-process " + path + " " + (end-start));
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "<-- PreProcess " + path + ": " +
					(end-start) + "ms");
		}
		
		SVDBFileTree ft = pp_out.getFileTree();

		start = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> Parse " + path);
		}
		SVDBFile file = f.parse(pp_out, path, markers);
		end = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "<-- Parse " + path + ": " +
					(end-start) + "ms");
		}
//		System.out.println("Parse " + path + " " + (end-start));

		start = System.currentTimeMillis();
		cacheDeclarations(build_data, file, ft);
		end = System.currentTimeMillis();
//		System.out.println("CacheDecl " + path + " " + (end-start));
		
		start = System.currentTimeMillis();
		build_data.fCache.setFile(path, file, false);
		build_data.fCache.setFileTree(path, ft, false);
		build_data.fCache.setMarkers(path, markers, false);

		end = System.currentTimeMillis();
//		System.out.println("SetCache " + path + " " + (end-start));
	}
	
	private void buildIndex(
			IProgressMonitor 				monitor,
			SVDBArgFileIndexBuildData		build_data) {
		long start_time, end_time;
		int total_work = 10000;
		int per_file_work = 0;
		
		monitor.beginTask("Build Index", total_work);

		// First, parse the argument files
		start_time = System.currentTimeMillis();
//		System.out.println("--> discoverRootFiles");
		discoverRootFiles(new SubProgressMonitor(monitor, 100), build_data);
		end_time = System.currentTimeMillis();
//		System.out.println("<-- discoverRootFiles " + (end_time-start_time));

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse argument files -- " + (end_time - start_time)
					+ "ms");
		}

		// Next, parse each of the discovered file paths
		List<String> paths = build_data.fIndexCacheData.fRootFileList;

//		System.out.println("--> parseFiles");
		start_time = System.currentTimeMillis();
	
		if (paths.size() > 0) {
			per_file_work = (total_work / paths.size());
		}
		if (per_file_work == 0) {
			per_file_work = 1;
		}
		
		for (int i=0; i<paths.size(); i++) {
			String path = paths.get(i);
			
			if (fDebugEn) {
				fLog.debug("Path: " + path);
			}
			
			long start_time_1 = System.currentTimeMillis();
			
			if (fFileSystemProvider.fileExists(path)) {
				monitor.subTask("Parse " + path);
//				System.out.println("--> parseFile " + path);
				parseFile(path, build_data);
				monitor.worked(per_file_work);
				long end_time_1 = System.currentTimeMillis();
//				System.out.println("Full Parse: " + path + " " + (end_time_1-start_time_1));
			}
		}
		end_time = System.currentTimeMillis();
		System.out.println("parseFiles " + paths.size() + " " + (end_time-start_time));
	
		// TODO: move this elsewhere (post-application of new data)
		synchronized (fIndexChangeListeners) {
			for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
				l.index_rebuilt();
			}
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse source files -- " + (end_time - start_time)
					+ "ms");
		}
		
		monitor.done();
	}

	public ISVPreProcessor createPreProcScanner(String path) {
		SVPreProcessor2 ret = null;
		
		ensureIndexUpToDate(new NullProgressMonitor());
		SVDBFileTree ft = findTargetFileTree(path);
		
//		System.out.println("ft=" + ft);
		
		if (ft != null) {
			List<SVDBFileTree> ft_l = new ArrayList<SVDBFileTree>();
		
			InputStream in = fFileSystemProvider.openStream(path);
			ret = new SVPreProcessor2(ft.getFilePath(), in, null, null);
			
			while (ft != null) {
				ft_l.add(ft);
				ft = (SVDBFileTree)ft.fParent;
			}

			// Do not include macros from the target file
			for (int i=ft_l.size()-1; i>=1; i--) {
				SVDBFileTree ft_t = ft_l.get(i);
				for (Entry<String, String> e : ft_t.fReferencedMacros.entrySet()) {
					ret.setMacro(e.getKey(), e.getValue());
				}
			}
		}

		return ret;
	}

	public String getFileFromId(int fileid) {
		return fBuildData.mapFileIdToPath(fileid);
	}

	private ISVPreProcFileMapper fReadOnlyFileMapper = new ISVPreProcFileMapper() {
		
		public int mapFilePathToId(String path, boolean add) {
			return SVDBArgFileIndex2.this.fBuildData.mapFilePathToId(path, false);
		}
		
		public String mapFileIdToPath(int id) {
			return SVDBArgFileIndex2.this.fBuildData.mapFileIdToPath(id);
		}
	};
	
}
