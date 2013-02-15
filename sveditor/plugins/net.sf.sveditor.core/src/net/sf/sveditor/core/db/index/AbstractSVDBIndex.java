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
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Pattern;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefFinder;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
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
import net.sf.sveditor.core.preproc.SVPreProcDirectiveScanner;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.SubProgressMonitor;

public abstract class AbstractSVDBIndex implements 
		ISVDBIndex, ISVDBIndexInt, 
		ISVDBRefFinder, ISVDBFileSystemChangeListener, 
		ILogLevelListener, ILogLevel  {
	private static final int IndexState_AllInvalid 			= 0;
	private static final int IndexState_RootFilesDiscovered	= (IndexState_AllInvalid + 1);
	private static final int IndexState_FilesPreProcessed	= (IndexState_RootFilesDiscovered + 1);
	private static final int IndexState_FileTreeValid 		= (IndexState_FilesPreProcessed + 1);
	private static final int IndexState_AllFilesParsed 		= (IndexState_FileTreeValid + 1);

	public  String 									fProjectName;
	private IProject								fProject;
	private String 									fBaseLocation;
	private String 									fResolvedBaseLocation;
	private String 									fBaseLocationDir;

	private SVDBBaseIndexCacheData 					fIndexCacheData;
	private boolean								fCacheDataValid;
	
	protected Set<String>							fMissingIncludes;
	
	// 
	// Map of filename to list of package names
	// Used to track files that have not yet been processed, and whose
	// content will need to be added to the package content cache
	// 
	protected List<Tuple<String, List<String>>>	fDeferredPkgCacheFiles;

	private ISVDBIncludeFileProvider 				fIncludeFileProvider;

	private List<ISVDBIndexChangeListener>			fIndexChangeListeners;

	protected static Pattern 						fWinPathPattern;
	protected LogHandle 							fLog;
	private ISVDBFileSystemProvider 				fFileSystemProvider;

	protected boolean 							fLoadUpToDate;
	private ISVDBIndexCache 						fCache;
	
	private SVDBIndexConfig	 						fConfig;
	
	// Manages a list of the directories that managed files are stored in
	private Set<String>								fFileDirs;
	
	// Controls indexing parallelism
	private int									fMaxIndexThreads = 0;
	protected boolean								fDebugEn;

	protected boolean								fInWorkspaceOk;

	/**
	 * True if the root file list is valid.
	 */
	private int 									fIndexState;
	protected boolean								fAutoRebuildEn;
	protected boolean								fIsDirty;

	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	protected AbstractSVDBIndex(String project) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle(getLogName());
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fMissingIncludes = new HashSet<String>();
		fMaxIndexThreads = SVCorePlugin.getMaxIndexThreads();
		fAutoRebuildEn = true;
		
		fFileDirs = new HashSet<String>();
		fDeferredPkgCacheFiles = new ArrayList<Tuple<String,List<String>>>();
		
		// Try to obtain the project handle
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			fProject = root.getProject(fProjectName);
		} catch (IllegalStateException e) {}
	}

	public AbstractSVDBIndex(String project, String base_location,
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

	protected abstract String getLogName();

	/**
	 * Called when the index is initialized to determine whether the cached
	 * information is still valid
	 * 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	protected boolean checkCacheValid() {
		boolean valid = true;
		String version = SVCorePlugin.getVersion();
		
		if (fDebugEn) {
			fLog.debug("Cached version=" + fIndexCacheData.getVersion() + " version=" + version);
		}
		
		if (fIndexCacheData.getVersion() == null ||
				!fIndexCacheData.getVersion().equals(version)) {
			valid = false;
			return valid;
		}
		
		// Confirm that global defines are the same
		if (fConfig != null) {
			// First check to see if all configured global defines are present
			if (fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = 
						(Map<String, String>)fConfig.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				if (define_map.size() != fIndexCacheData.getGlobalDefines().size()) {
					if (fDebugEn) {
						fLog.debug(LEVEL_MID, "Cache invalid -- size of global defines is different");
					}
					valid = false;
				} else {
					// Check all defines
					for (Entry<String, String> e : define_map.entrySet()) {
						if (fIndexCacheData.getGlobalDefines().containsKey(e.getKey())) {
							if (!fIndexCacheData.getGlobalDefines().get(e.getKey()).equals(e.getValue())) {
								if (fDebugEn) {
									fLog.debug(LEVEL_MID, "Cache invalid -- define " +
										e.getKey() + " has a different value");
								}
								valid = false;
								break;
							}
						} else {
							if (fDebugEn) {
								fLog.debug(LEVEL_MID, "Cache invalid -- define " +
										e.getKey() + " not in cache");
							}
							valid = false;
							break;
						}
					}
				}
			} else if (fIndexCacheData.getGlobalDefines().size() > 0) {
				// Local index has defines and the incoming config does not
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "Cache invalid -- no global defines, and cache has");
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
						fLog.debug(LEVEL_MIN, "Cache is invalid due to timestamp on " + path +
								": file=" + fs_timestamp + " cache=" + cache_timestamp);
					}
					valid = false;
					break;
				}
			}
		} else {
			if (fDebugEn) {
				fLog.debug(LEVEL_MIN, "Cache " + getBaseLocation() + " is invalid -- 0 entries");
			}
			SVDBIndexFactoryUtils.setBaseProperties(fConfig, this);
			valid = false;
		}
		
		if (getCacheData().getMissingIncludeFiles().size() > 0 && valid) {
			if (fDebugEn) {
				fLog.debug("Checking missing-include list added files");
			}
			for (String path : getCacheData().getMissingIncludeFiles()) {
				SVDBSearchResult<SVDBFile> res = findIncludedFile(path);
				if (res != null) {
					if (fDebugEn) {
						fLog.debug(LEVEL_MIN, "Cache " + getBaseLocation() + 
								" is invalid since previously-missing include file is now found: " +
								path);
					}
					valid = false;
					break;
				}
			}
		}
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "[AbstractSVDBIndex] Cache " + getBaseLocation() + " is " + ((valid)?"valid":"invalid"));
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
		fIndexCacheData = createIndexCacheData();
		fCacheDataValid = fCache.init(m, fIndexCacheData, fBaseLocation);

		if (fCacheDataValid) {
			fCacheDataValid = checkCacheValid();
		}

		if (fCacheDataValid) {
			if (fDebugEn) {
				fLog.debug("Cache is valid");
			}
			fIndexState = IndexState_FileTreeValid;
			
			// If we've determined the index data is valid, then we need to fixup some index entries
			if (fIndexCacheData.getDeclCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : 
						fIndexCacheData.getDeclCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}
			
			// Also update the package cache
			if (fIndexCacheData.getPackageCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e :
					fIndexCacheData.getPackageCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}
			
			// Also re-set filenames on the reference cache
			if (fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : fIndexCacheData.getReferenceCacheMap().entrySet()) {
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
	
	public synchronized void loadIndex(IProgressMonitor monitor) {
		ensureIndexState(monitor, IndexState_AllFilesParsed);
	}
	
	public synchronized boolean isLoaded() {
		return (fIndexState >= IndexState_AllFilesParsed);
	}
	
	public synchronized boolean isFileListLoaded() {
		return (fIndexState >= IndexState_FileTreeValid);
	}

	/**
	 * @param monitor
	 * @param state
	 */
	public synchronized void ensureIndexState(IProgressMonitor monitor, int state) {
		long start_time=0, end_time=0;
		// The following weights are an attempt to skew the "amount of work" between the different states
		// I came up these weights by looking at how long each of these tasks took on a SINGLE project
		// and came up with the following.  
		// There is probably a better way to do this, but this is better than what we had previously 
		// where the time taken to Discover root files was 100th the time to get a valid file tree, 
		// but the monitor itself was incrementing equally on both steps
		final int monitor_weight_RootFilesDiscovered = 2;
		final int monitor_weight_FilesPreProcessed   = 8;
		final int monitor_weight_FileTreeValid       = 80;
		final int monitor_weight_AllFilesParsed      = 10;
		monitor.beginTask("Ensure Index State for " + getBaseLocation(), 100); // discover_root_files+preprocessFiles+buildFileTree+initLoad
		fLog.debug(LEVEL_MID, "ensureIndexState0 Starting Ensure Index State");
	
		if (fIndexState < state) {
			fLog.debug(LEVEL_MIN, "ensureIndexState " + getBaseLocation() + 
					" " + fIndexState + " => " + state);
		}
		
		if (fIndexState < IndexState_RootFilesDiscovered
				&& state >= IndexState_RootFilesDiscovered) {
			if (fDebugEn) {
				fLog.debug("Moving index " + getBaseLocation() + 
						" to state RootFilesDiscovered from " + fIndexState);
				start_time = System.currentTimeMillis();
			}
			discoverRootFiles(new SubProgressMonitor(monitor, monitor_weight_RootFilesDiscovered));
			// Flush file-list back to backing store
			fCache.sync();
			fIndexState = IndexState_RootFilesDiscovered;
			fIsDirty = false;
			if (fDebugEn) {
				end_time = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "ensureIndexState1 Move to RootFilesDiscovered: " + (end_time-start_time)/1000);
			}
		}
		else  {
			monitor.worked(monitor_weight_RootFilesDiscovered);
		}
		if (fIndexState < IndexState_FilesPreProcessed
				&& state >= IndexState_FilesPreProcessed) {
			if (fDebugEn) {
				fLog.debug("Moving index " + getBaseLocation() +
						" to state FilesPreProcessed from " + fIndexState);
				start_time = System.currentTimeMillis();
			}
			preProcessFiles(new SubProgressMonitor(monitor, monitor_weight_FilesPreProcessed));
			fIndexState = IndexState_FilesPreProcessed;
			fIsDirty = false;
			
			if (fDebugEn) {
				end_time = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "ensureIndexState2 Move to FilesPreProcessed: " + (end_time-start_time)/1000);
			}
		}
		else  {
			monitor.worked(monitor_weight_FilesPreProcessed);
		}
		if (fIndexState < IndexState_FileTreeValid
				&& state >= IndexState_FileTreeValid) {
			if (fDebugEn) {
				fLog.debug("Moving index " + getBaseLocation() +
						" to state FileTreeValid from " + fIndexState);
				start_time = System.currentTimeMillis();
			}
			buildFileTree(new SubProgressMonitor(monitor, monitor_weight_FileTreeValid));
			fIndexState = IndexState_FileTreeValid;
			
			propagateAllMarkers();
			notifyIndexRebuilt();
			fIsDirty = false;
			
			if (fDebugEn) {
				end_time = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "ensureIndexState3 Move to FileTreeValid: " + (end_time-start_time)/1000);
			}
		}
		else  {
			monitor.worked(monitor_weight_FileTreeValid);
		}
		if (fIndexState < IndexState_AllFilesParsed
				&& state >= IndexState_AllFilesParsed) {
			if (fDebugEn) {
				start_time = System.currentTimeMillis();
				fLog.debug("Moving index " + getBaseLocation() +
						" to state AllFilesParsed from " + fIndexState);
			}
			
			if (fCacheDataValid) {
				fCache.initLoad(new SubProgressMonitor(monitor, monitor_weight_AllFilesParsed));
			} else {
				parseFiles(new SubProgressMonitor(monitor, monitor_weight_AllFilesParsed));
			}
			fIndexState = IndexState_AllFilesParsed;
			notifyIndexRebuilt();
			fIsDirty = false;
			synchronized (fDeferredPkgCacheFiles) {
				for (Tuple<String, List<String>> e : fDeferredPkgCacheFiles) {
					if (e.second().size() > 0) {
						fLog.debug("WARNING: deferred package-include file " + e.first() + " not located");
						for (String pkg : e.second()) {
							fLog.debug("  Package: " + pkg);
						}
					}
				}
			}
			
			if (fDebugEn) {
				fLog.debug(LEVEL_MID, "ensureIndexState4 Move to AllFilesParsed: " + (end_time-start_time)/1000);
			}
		}
		else  {
			monitor.worked(monitor_weight_AllFilesParsed);
		}
	
		
		monitor.done();
	}

	/**
	 * pre-conditions:
	 * - discoverFiles
	 * - preProcessFiles
	 * - 
	 * @param monitor
	 */
	protected void parseFiles(IProgressMonitor monitor) {
		final List<String> paths = new ArrayList<String>();
//		final List<IJob> jobs = new ArrayList<IJob>();
		
		fLog.debug(LEVEL_MIN, "parseFiles " + getBaseLocation());
		
		synchronized (fCache) {
			paths.addAll(fCache.getFileList(false));
		}
		monitor.beginTask("Parsing Files", paths.size());

		/*
		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		
		for (String path : paths) {
			ParseFilesRunnable r = new ParseFilesRunnable(path, m);
			IJob j = job_mgr.createJob();
			j.init(path, r);
			job_mgr.queueJob(j);
			jobs.add(j);
		}
		
		// Now, wait for all jobs to complete
		synchronized (jobs) {
			for (IJob j : jobs) {
				j.join();
			}
		}
		 */
		
		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			parseFilesJob(paths, new SubProgressMonitor(monitor, paths.size()));
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				final SubProgressMonitor spm;
				spm = new SubProgressMonitor(monitor, paths.size()/threads.length);
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						
						// TODO: This is wrong!!! need to change to a new SubProgressMonitor(monitor, paths.size())
						parseFilesJob(paths, spm);
					}
				}, "parse_" + getBaseLocation() + "_" + i);
				threads[i].setPriority(Thread.MAX_PRIORITY);
				threads[i].start();
			}
			
			// Now, wait for the threads to complete
			join_threads(threads);
		}
		
		monitor.done();
	}
	
	protected void parseFilesJob(List<String> paths, IProgressMonitor monitor) {
		monitor.beginTask("parseFilesJob", paths.size());
		while (true) {
			String path = null;
			synchronized(paths) {
				if (paths.size() > 0) {
					path = paths.remove(0);
				}
			}
			
			if (path == null) {
				break;
			}
			
			SVDBFile ret;

			synchronized (fCache) {
				ret = fCache.getFile(new NullProgressMonitor(), path);
			}

			if (ret == null) {
				SVDBFileTree ft_root;
				synchronized (fCache) {
					ft_root = fCache.getFileTree(new NullProgressMonitor(), path, false);
				}
				
				if (ft_root == null) {
					try {
						throw new Exception();
					} catch (Exception e) {
						fLog.error("File Path \"" + path + "\" not in index " +
								getBaseLocation(), 
								e);
						for (String p : getFileList(new NullProgressMonitor())) {
							fLog.error("path: " + p);
						}
					}
						
				} 
				if(ft_root != null) {
					IPreProcMacroProvider mp = createMacroProvider(ft_root);
					processFile(ft_root, mp);
				}
				
				synchronized (fCache) {
					ret = fCache.getFile(new NullProgressMonitor(), path);
				}
			}

			monitor.worked(1);
		}
		monitor.done();
	}

	protected synchronized void invalidateIndex(IProgressMonitor monitor, String reason, boolean force) {
		monitor.beginTask("invalidateIndex", 1);
		if (fDebugEn) {
			if (fAutoRebuildEn || force) {
				fLog.debug(LEVEL_MIN, "InvalidateIndex " + getBaseLocation() + ": " +
						((reason == null)?"No reason given":reason));
			} else {
				fLog.debug(LEVEL_MIN, "InvalidateIndex " + getBaseLocation() + ": " +
						((reason == null)?"No reason given":reason) + 
						" (ignored -- AutoRebuild disabled)");
			}
		}
		
		if (fAutoRebuildEn || force) {
			if (fIndexState != IndexState_AllInvalid) {
				fIndexState = IndexState_AllInvalid;
				fCacheDataValid = false;
				fIndexCacheData.clear();
				fCache.clear(new SubProgressMonitor(monitor, 1));
				fMissingIncludes.clear();
				fDeferredPkgCacheFiles.clear();
			}
		} else {
			fIsDirty = true;
			monitor.worked(1);
		}
		monitor.done();
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

	protected SVDBBaseIndexCacheData getCacheData() {
		return fIndexCacheData;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		if (fFileSystemProvider != null && fs_provider != fFileSystemProvider) {
			fFileSystemProvider.removeFileSystemChangeListener(this);
		}
		fFileSystemProvider = fs_provider;

		if (fFileSystemProvider != null) {
			fFileSystemProvider.init(getResolvedBaseLocationDir());
			fFileSystemProvider.addFileSystemChangeListener(this);
		}
	}

	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}

	public void fileChanged(String path) {
		synchronized (fCache) {
			if (fCache.getFileList(false).contains(path)) {
//				invalidateIndex();
				if (fDebugEn) {
					fLog.debug(LEVEL_MIN, "fileChanged: " + path);
				}
				fCache.setFile(path, null, false);
				fCache.setLastModified(path, 
						getFileSystemProvider().getLastModifiedTime(path), false);
			}
		}
	}

	public void fileRemoved(String path) {
		boolean invalidate = false;
		synchronized (fCache) {
			invalidate = fCache.getFileList(false).contains(path);
		}
		
		if (invalidate) {
			invalidateIndex(new NullProgressMonitor(), "File Removed", false);
		}
	}

	public void fileAdded(String path) {
		// TODO: Not sure what to do with this one
		// Just for safety, invalidate the index when files are added
		File f = new File(path);
		File p = f.getParentFile();
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "fileAdded: " + path);
		}
		
		if (fFileDirs.contains(p.getPath())) {
			invalidateIndex(new NullProgressMonitor(), "File Added", false);
		}
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
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(
					fBaseLocation, fProjectName, fInWorkspaceOk);
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

	protected void clearDefines() {
		fIndexCacheData.clearDefines();
	}

	protected void addDefine(String key, String val) {
		fIndexCacheData.addDefine(key, val);
	}

	protected void clearIncludePaths() {
		fIndexCacheData.clearIncludePaths();
	}

	protected void addIncludePath(String path) {
		fIndexCacheData.addIncludePath(path);
	}

	/**
	 * getFileList() -- returns a list of files handled by this index The file
	 * list is valid after: - Root File discovery - Pre-processor parse
	 */
	public synchronized Iterable<String> getFileList(IProgressMonitor monitor) {
		ensureIndexState(monitor, IndexState_FileTreeValid);
		return fCache.getFileList(false);
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
		monitor.beginTask("findFile", 5);		// ensureIndexState, PATFHM_WORKSPACE, PATHFMT_FILESYSTEM + getFileTree + getFile
		ensureIndexState(new SubProgressMonitor(monitor, 1), IndexState_FileTreeValid);

		for (String fmt : new String[] {null, 
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM}) {
			if (fmt != null) {
				r_path = fFileSystemProvider.resolvePath(path, fmt);
			}
			synchronized (fCache) {
				ret = fCache.getFile(new SubProgressMonitor(monitor, 1), r_path);
			}
			
			if (ret != null) {
				break;
			}
		}

		if (ret == null) {
			SVDBFileTree ft_root;
			synchronized (fCache) {
				ft_root = fCache.getFileTree(new SubProgressMonitor(monitor, 1), path, false);
			}

			if (ft_root != null) {
				IPreProcMacroProvider mp = createMacroProvider(ft_root);
				processFile(ft_root, mp);
				
				synchronized (fCache) {
					ret = fCache.getFile(new SubProgressMonitor(monitor, 1), path);
				}
			} else {
				monitor.worked(1);
				/*
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.error("File Path \"" + path + "\" not in index", e);
					for (String p : getFileList(monitor)) {
						System.out.println("path: " + p);
					}
				}
				 */
			}
		}
		else  {
			monitor.worked(1);
		}

		/*
		if (ret == null) {
			try {
				throw new Exception("File \"" + path + "\" not found");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		 */
		
		if (fDebugEn) {
			fLog.debug("--> findFile: " + path + " ret=" + ret);
		}
		monitor.done();

		return ret;
	}

	/**
	 * Implementation of ISVDBIndexIterator method
	 */
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		String r_path = path;
		SVDBFile file = null;

		ensureIndexState(monitor, IndexState_FileTreeValid);
		
		// Cycle through the various path formats
		for (String fmt : new String[] {null, 
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM}) {
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
			
	
	public synchronized List<SVDBMarker> getMarkers(String path) {
		/*SVDBFile file = */findFile(path);

		List<SVDBMarker> markers = fCache.getMarkers(path);
		
		if (fDebugEn) {
			fLog.debug("markers for " + path + ": " + 
					((markers != null)?markers.size():"null"));
		}
		
		return markers;
	}

	protected void addFile(String path, boolean is_argfile) {
		fLog.debug("addFile: " + path);
		synchronized (fCache) {
			fCache.addFile(path, is_argfile);
			fCache.setLastModified(path, getFileSystemProvider().getLastModifiedTime(path), is_argfile);
		}
		
		addFileDir(path);
	}
	
	protected void addFileDir(String file_path) {
		File f = new File(file_path);
		File p = f.getParentFile();
		
		if (p != null && !fFileDirs.contains(p.getPath())) {
			fFileDirs.add(p.getPath());
		}
	}

	protected void clearFilesList() {
		fLog.debug("clearFilesList");
		fCache.clear(new NullProgressMonitor());
		fFileDirs.clear();
	}

	protected void propagateAllMarkers() {
		for (boolean is_argfile : new boolean[] {false, true}) {
			Set<String> file_list = fCache.getFileList(is_argfile);
			for (String path : file_list) {
				if (path != null) {
					propagateMarkers(path);
				}
			}
		}
	}
	
	protected void propagateMarkers(String path) {
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
	
	/**
	 * Creates
	 * 
	 * @return
	 */
	protected SVDBBaseIndexCacheData createIndexCacheData() {
		return new SVDBBaseIndexCacheData(getBaseLocation());
	}

	/**
	 * 
	 * @param monitor
	 */
	protected abstract void discoverRootFiles(IProgressMonitor monitor);

	/**
	 * 
	 */
	protected void preProcessFiles(final IProgressMonitor monitor) {
		final List<String> paths = new ArrayList<String>();
		
		fLog.debug(LEVEL_MIN, "preProcessFiles " + getBaseLocation());
		
		synchronized (fCache) {
			paths.addAll(fCache.getFileList(false));
		}
		
		monitor.beginTask("Pre-Process Files", paths.size());

		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			preProcessFilesJob(paths, new SubProgressMonitor(monitor, paths.size()));
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				final SubProgressMonitor spm;
				spm = new SubProgressMonitor(monitor, paths.size()/threads.length);
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						preProcessFilesJob(paths, spm);
					}	
				});
				threads[i].start();
			}
			
			// Now, wait for the threads to complete
			join_threads(threads);
		}
		
		monitor.done();
	}
	
	private void join_threads(Thread threads[]) {
		for (int i=0; i<threads.length; i++) {
			if (threads[i].isAlive()) {
				try {
					threads[i].join();
				} catch (InterruptedException e) {}
			}
		}
	}
	
	protected void preProcessFilesJob(List<String> paths, IProgressMonitor monitor) {
		monitor.beginTask("preProcessFilesJob", paths.size());
		while (true) {
			String path = null;
			synchronized(paths) {
				if (paths.size() > 0) {
					path = paths.remove(0);
				}
			}
			// Reached the end of the list
			if (path == null) {
				break;
			}
			
			SVDBFile file = processPreProcFile(path);
			synchronized (fCache) {
				if (file != null) {
					fCache.setPreProcFile(path, file);
					fCache.setLastModified(path, 
							fFileSystemProvider.getLastModifiedTime(path), false);
				}
			}
			monitor.worked(1);
		}
		monitor.done();
	}

	protected void buildFileTree(final IProgressMonitor monitor) {
		final List<String> paths = new ArrayList<String>(); 
		paths.addAll(getCache().getFileList(false));
		final List<String> missing_includes = new ArrayList<String>();
	
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "buildFileTree " + getBaseLocation());
			for (String path : paths) {
				fLog.debug("  path: " + path);
			}
		}
		
		monitor.beginTask("Building File Tree", paths.size());
		
		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			buildFileTreeJob(paths, missing_includes, new SubProgressMonitor(monitor, paths.size()));
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				final SubProgressMonitor spm;
				spm = new SubProgressMonitor(monitor, paths.size()/threads.length);
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						// TODO: pretty sure this isn't right!!!
						buildFileTreeJob(paths, missing_includes, spm);
					}
				}, "file_tree-" + getBaseLocation() + "-" + i);
				threads[i].start();
			}
			
			// Now, wait for the threads to complete
			boolean threads_alive = true;
			while (threads_alive) {
				threads_alive = false;
				for (int i=0; i<threads.length; i++) {
					if (threads[i].isAlive()) {
						try {
							threads[i].join();
						} catch (InterruptedException e) {
							e.printStackTrace();
							threads_alive = true;
						}
					}
				}
			}
		}

		getCacheData().clearMissingIncludeFiles();
		for (String path : missing_includes) {
			getCacheData().addMissingIncludeFile(path);
		}

		monitor.done();
	}
	
	protected void buildFileTreeJob(
			List<String>			paths,
			List<String>			missing_includes,
			IProgressMonitor		monitor) {
		synchronized(paths) {
			monitor.beginTask("buildFileTreeJob", paths.size()*2);		// getFileTree + getPreProcFile
		}
		while (true) {
			String path = null;
			synchronized(paths) {
				if (paths.size() > 0) {
					path = paths.remove(0);
				}
			}
			
			if (path == null) {
				break;
			}
			
			synchronized (fCache) {
				if (fCache.getFileTree(new SubProgressMonitor(monitor, 1), path, false) != null) {
					continue;
				}
			}
			
			SVDBFile pp_file ;

			synchronized (fCache) {
				pp_file = fCache.getPreProcFile(
						new SubProgressMonitor(monitor, 1), path);
				
			}
				
			if (pp_file == null) {
				Exception e = null;
				try {
					throw new Exception();
				} catch (Exception ex) {
					e = ex;
				}
				fLog.error("Failed to get pp_file \"" + path + "\" from cache", e);
			} else {
				SVDBFileTree ft_root = new SVDBFileTree( (SVDBFile) pp_file.duplicate());
				Set<String> included_files = new HashSet<String>();
				Map<String, SVDBFileTree> working_set = new HashMap<String, SVDBFileTree>();
				buildPreProcFileMap(null, ft_root, missing_includes, included_files, working_set, null, true);
			}
		}
		monitor.done();
	}

	protected void buildPreProcFileMap(
			SVDBFileTree 				parent, 
			SVDBFileTree 				root,
			List<String>				missing_includes,
			Set<String>					included_files,
			Map<String, SVDBFileTree>	working_set,
			List<SVDBMarker>			markers,
			boolean						update_cache) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();

		if (fDebugEn) {
			fLog.debug("buildPreProcFileMap " + root.getFilePath());
		}
		if (!working_set.containsKey(root.getFilePath())) {
			working_set.put(root.getFilePath(), root);
		}

		if (update_cache) {
			synchronized (fCache) {
				if (!working_set.containsKey(root.getFilePath())) {
					System.out.println("FileTree " + root.getFilePath() + " not in working set");
				}
				fCache.setFileTree(root.getFilePath(), root, false);
			}
		}

		if (parent != null) {
			root.getIncludedByFiles().add(parent.getFilePath());
		}

		synchronized (root) {
			ft_utils.resolveConditionals(root, new SVPreProcDefineProvider(
					createPreProcMacroProvider(root, working_set)));
		}

		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}
		included_files.add(root.getFilePath());
		addPreProcFileIncludeFiles(root, root.getSVDBFile(), markers, 
				missing_includes, included_files, working_set);

		if (update_cache) {
			synchronized (fCache) {
				if (root.getFilePath().endsWith(".f")) {
					try {
						throw new Exception();
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
				fCache.setFileTree(root.getFilePath(), root, false);
				if (fDebugEn) {
					fLog.debug("Setting markers (2) for " + root.getFilePath() + " " + markers.size());
				}
				fCache.setMarkers(root.getFilePath(), markers, false);
			}
		}
	}

	private void addPreProcFileIncludeFiles(
			SVDBFileTree 		root,
			ISVDBScopeItem 		scope,
			List<SVDBMarker>	markers,
			List<String>		missing_includes,
			Set<String>			included_files,
			Map<String, SVDBFileTree>	working_set) {
		for (int i = 0; i < scope.getItems().size(); i++) {
			ISVDBItemBase it = scope.getItems().get(i);

			if (it.getType() == SVDBItemType.Include) {
				if (fDebugEn) {
					fLog.debug("Include file: " + ((ISVDBNamedItem) it).getName());
				}

				// Look local first
				SVDBSearchResult<SVDBFile> f = findIncludedFileGlobal(((ISVDBNamedItem) it)
						.getName());

				if (f != null) {
					if (fDebugEn) {
						fLog.debug("Found include file \""
								+ ((ISVDBNamedItem) it).getName()
								+ "\" in index \"" + f.getIndex().getBaseLocation()
								+ "\"");
					}
					String file_path = f.getItem().getFilePath();
					if (fDebugEn) {
						fLog.debug("Adding included file \"" + file_path
								+ " to FileTree \"" + root.getFilePath() + "\"");
					}
					SVDBFileTree ft = new SVDBFileTree((SVDBFile) f.getItem().duplicate());
					root.addIncludedFile(ft.getFilePath());
					if (fDebugEn) {
						fLog.debug("    Now has " + ft.getIncludedFiles().size()
								+ " included files");
					}
					if (!included_files.contains(f.getItem().getFilePath())) {
						buildPreProcFileMap(root, ft, missing_includes, included_files, working_set, null, true);
					}
				} else {
					String missing_path = ((ISVDBNamedItem) it).getName();
					if (fDebugEn) {
						fLog.debug("Failed to find include file \""
								+ missing_path + "\" (from file " + root.getFilePath() + ")");
					}
					synchronized (missing_includes) {
						if (!missing_includes.contains(missing_path)) {
							missing_includes.add(missing_path);
						}
					}
					SVDBFileTree ft = new SVDBFileTree(SVDBItem.getName(it));
					root.addIncludedFile(ft.getFilePath());
					ft.getIncludedByFiles().add(root.getFilePath());

					// Create a marker for the missing include file
					SVDBMarker err = new SVDBMarker(MarkerType.Error,
							MarkerKind.MissingInclude,
							"Failed to find include file \""
									+ ((ISVDBNamedItem) it).getName()
									+ "\"");
					err.setLocation(it.getLocation());
					markers.add(err);
				}
			} else if (it instanceof ISVDBScopeItem) {
				addPreProcFileIncludeFiles(root, (ISVDBScopeItem) it, 
						markers, missing_includes, included_files,
						working_set);
			}
		}
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		SVDBFile file = null;
		
		if (fDebugEn) {
			fLog.debug("findIncludedFile: " + path);
		}
		
		if (fDebugEn) {
			fLog.debug("Checking pre-processor cache");
		}
		
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = resolvePath(inc_dir + "/" + path, fInWorkspaceOk);

			if (fDebugEn) {
				fLog.debug("Include Path: \"" + inc_path + "\"");
			}

			if ((file = fCache.getPreProcFile(new NullProgressMonitor(), inc_path)) != null) {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: \"" + inc_path
							+ "\" already in map");
				}
				break;
			}
		}
	
		if (file != null) {
			if (fDebugEn) {
				fLog.debug("findIncludedFile: File available from cache");
			}
			return new SVDBSearchResult<SVDBFile>(file, this);
		}
		
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = resolvePath(inc_dir + "/" + path, fInWorkspaceOk);
			if (fFileSystemProvider.fileExists(inc_path)) {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: building entry for \""
							+ inc_path + "\"");
				}

				file = processPreProcFile(inc_path);
				addFile(inc_path, true);
				fCache.setPreProcFile(inc_path, file);
				fCache.setLastModified(inc_path, 
						fFileSystemProvider.getLastModifiedTime(inc_path), false);
				break;
			} else {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: file \"" + inc_path
							+ "\" does not exist");
				}
			}
		}

		if (file != null) {
			if (fDebugEn) {
				fLog.debug("findIncludedFile: Found and parsed new include file");
			}
			return new SVDBSearchResult<SVDBFile>(file, this);
		}

		String res_path = resolvePath(path, fInWorkspaceOk);

		if (fFileSystemProvider.fileExists(res_path)) {
			SVDBFile pp_file = null;
			if ((pp_file = processPreProcFile(res_path)) != null) {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: adding file \"" + path + "\"");
				}
				addFile(res_path, true);
				return new SVDBSearchResult<SVDBFile>(pp_file, this);
			}
		}

		return null;
	}

	protected String resolvePath(String path_orig, boolean in_workspace_ok) {
		String path = path_orig;
		String norm_path = null;

		if (fDebugEn) {
			fLog.debug("--> resolvePath: " + path_orig);
		}

		// relative to the base location or one of the include paths
		if (path.startsWith("..")) {
			if (fDebugEn) {
				fLog.debug("    path starts with ..");
			}
			if ((norm_path = resolveRelativePath(getResolvedBaseLocationDir(),
					path)) == null) {
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					if (fDebugEn) {
						fLog.debug("    Check: " + inc_path + " ; " + path);
					}
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break;
					}
				}
			} else {
				if (fDebugEn) {
					fLog.debug("norm_path=" + norm_path);
				}
			}
		} else {
			if (path.equals(".")) {
				path = getResolvedBaseLocationDir();
			} else if (path.startsWith(".")) {
				path = getResolvedBaseLocationDir() + "/" + path.substring(2);
			} else {
				if (!fFileSystemProvider.fileExists(path)) {
					// See if this is an implicit path
					String imp_path = getResolvedBaseLocationDir() + "/" + path;
					if (fFileSystemProvider.fileExists(imp_path)) {
						// This path is an implicit relative path that is
						// relative to the base directory
						path = imp_path;
					}
				}
			}
			norm_path = normalizePath(path);
		}
		
		if (norm_path != null && !norm_path.startsWith("${workspace_loc}") && in_workspace_ok) {
			IWorkspaceRoot ws_root = null;
			
			try {
				ws_root = ResourcesPlugin.getWorkspace().getRoot();
				IFile file = ws_root.getFileForLocation(new Path(norm_path));
				if (file != null && file.exists()) {
					norm_path = "${workspace_loc}" + file.getFullPath().toOSString();
				}
			} catch (IllegalStateException e) {}
		}
		
		norm_path = (norm_path != null) ? norm_path : path_orig;
		
		if (fDebugEn) {
			fLog.debug("<-- resolvePath: " + path_orig + " " + norm_path);
		}

		return norm_path;
	}

	private String resolveRelativePath(String base, String path) {
		String ret = null;
		if (fDebugEn) {
			fLog.debug("--> resolveRelativePath: base=" + base + " path=" + path);
		}
		
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base + "/" + path);

		if (fDebugEn) {
			fLog.debug("    Checking normalizedPath: " + norm_path
					+ " ; ResolvedBaseLocation: " + getResolvedBaseLocationDir());
		}

		if (fFileSystemProvider.fileExists(norm_path)) {
			ret = norm_path;
		} else if (getBaseLocation().startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path
			// by computing the absolute path
			String base_loc = getResolvedBaseLocationDir();
			if (fDebugEn) {
				fLog.debug("Possible outside-workspace path: " + base_loc);
			}
			base_loc = base_loc.substring("${workspace_loc}".length());

			if (fDebugEn) {
				fLog.debug("    base_loc: " + base_loc);
			}

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer base_dir = null;
			try {
				base_dir = root.getFolder(new Path(base_loc));
			} catch (IllegalArgumentException e) {
			}

			if (base_dir == null) {
				if (base_loc.length() > 0) {
					base_dir = root.getProject(base_loc.substring(1));
				}
			}

			if (fDebugEn) {
				fLog.debug("base_dir=" + ((base_dir != null)?base_dir.getFullPath().toOSString():null));
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					if (fDebugEn) {
						fLog.debug("Location of base_dir: " + base_dir_p.toOSString());
					}
					File path_f_t = new File(base_dir_p.toFile(), path);
					if (fDebugEn) {
						fLog.debug("Checking if path exists: " + path_f_t.getAbsolutePath() + " " + path_f_t.exists());
					}
					try {
						if (path_f_t.exists()) {
							if (fDebugEn) {
								fLog.debug("Path does exist outside the project: "
										+ path_f_t.getCanonicalPath());
							}
							norm_path = SVFileUtils.normalize(path_f_t
									.getCanonicalPath());
							ret = norm_path;
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- resolveRelativePath: base=" + base + " path=" + path + " ret=" + ret);
		}
		return ret;
	}

	protected String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();

		int i = path.length() - 1;
		int end;
		int skipCnt = 0;

		// First, skip any trailing '/'
		while (i >= 0 && (path.charAt(i) == '/' || path.charAt(i) == '\\')) {
			i--;
		}

		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();

			while (i >= 0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}

			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length() - 1);
				if (str.equals("..")) {
					skipCnt++;
					// remove .. element
					ret.setLength(end);
				} else if (skipCnt > 0) {
					ret.setLength(end);
					skipCnt--;
				}
			}
		}

		return ret.reverse().toString();
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider provider) {
		fIncludeFileProvider = provider;
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

	protected void notifyIndexRebuilt() {
		synchronized (fIndexChangeListeners) {
			for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
				l.index_rebuilt();
			}
		}
	}

	protected IPreProcMacroProvider createMacroProvider(SVDBFileTree file_tree) {
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(fCache, file_tree, fMissingIncludes);

		for (Entry<String, String> entry : fIndexCacheData.getGlobalDefines()
				.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		for (Entry<String, String> entry : fIndexCacheData.getDefines()
				.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}

		return mp;
	}

	protected IPreProcMacroProvider createPreProcMacroProvider(
			SVDBFileTree 					file,
			Map<String, SVDBFileTree>		working_set) {
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(
				fCache, working_set);
		mp.setFileContext(file);

		for (Entry<String, String> entry : fIndexCacheData.getGlobalDefines()
				.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		for (Entry<String, String> entry : fIndexCacheData.getDefines()
				.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}

		return mp;
	}

	public SVDBSearchResult<SVDBFile> findIncludedFileGlobal(String leaf) {
		SVDBSearchResult<SVDBFile> ret = findIncludedFile(leaf);

		if (ret == null) {
			if (fIncludeFileProvider != null) {
				ret = fIncludeFileProvider.findIncludedFile(leaf);
				if (fDebugEn) {
					fLog.debug("Searching for \"" + leaf + "\" in global (ret="
							+ ret + ")");
				}
			} else {
				if (fDebugEn) {
					fLog.debug("IncludeFileProvider not set");
				}
			}
		}

		return ret;
	}

	public Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor	monitor, 
			InputStream 		in,
			String 				path, 
			List<SVDBMarker>	markers) {
		if (monitor == null)
			monitor = new NullProgressMonitor();
		monitor.beginTask("parse" , 1);
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
				invalidateIndex(new NullProgressMonitor(), "Failed to find FileTree for " + path, false);
				addFile(path, true);
				file_tree = findFileTree(path, false);
				
				// If auto-rebuild is disabled, then we do 
				// a bit more work to create a reasonable representation
				// of the new file.
				if (file_tree == null && !fAutoRebuildEn) {
					file_tree = incrCreateFileTree(path);
				}
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
		buildPreProcFileMap(null, file_tree, missing_includes, included_files, working_set, markers, false);
		
		markers.clear();
		
		// TODO: Need to be more intelligent about this
		/*
		List<SVDBMarker> markers_e = fCache.getMarkers(path); 
		if (markers_e != null) {
		 */
			for (SVDBMarker m : markers_e) {
				if (m.getKind() == MarkerKind.MissingInclude) {
					markers.add(m);
				}
			}
			/*
		}
		 */

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

//		fFileSystemProvider.clearMarkers(file_tree.getFilePath());
		file_tree.setSVDBFile(svdb_pp);
		// addIncludeFiles(file_tree, file_tree.getSVDBFile());
		
		if (file_tree.getFilePath() == null) {
			System.out.println("file_tree path: " + path + " is null");
		}

		dp.setMacroProvider(createMacroProvider(file_tree));
		SVDBFile svdb_f = factory.parse(
				copier.copy(), file_tree.getFilePath(), markers);
		
		if (svdb_f.getFilePath() == null) {
			System.out.println("file path: " + path + " is null");
		}
		/** TMP:
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		 */

		// propagateMarkersPreProc2DB(file_tree, svdb_pp, svdb_f);
		// addMarkers(path, svdb_f);
		monitor.worked(1);
		monitor.done();
		return new Tuple<SVDBFile, SVDBFile>(svdb_pp, svdb_f);
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	protected void processFile(SVDBFileTree path, IPreProcMacroProvider mp) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);
		
		fLog.debug(LEVEL_MAX, "processFile: " + path.getFilePath());

		String path_s = path.getFilePath();

		InputStream in = fFileSystemProvider.openStream(path_s);

		if (in == null) {
			fLog.error("ProcessFile: Failed to open file \"" + path_s + "\"");
		}

		List<SVDBMarker> markers = fCache.getMarkers(path.getFilePath());
		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}

		// Remove any undefined-macro or parse errors
		for (int i = 0; i < markers.size(); i++) {
			if (markers.get(i).getKind() == MarkerKind.UndefinedMacro
					|| markers.get(i).getKind() == MarkerKind.ParseError) {
				markers.remove(i);
				i--;
			}
		}

		SVDBFile svdb_f = factory.parse(in, path.getFilePath(), markers);

		// Problem parsing the file..
		if (svdb_f == null) {
			return;
		}
		
		/** TMP:
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path
				.getFilePath()));
		 */

		fFileSystemProvider.clearMarkers(path_s);

		synchronized (fCache) {
			fCache.setFile(path.getFilePath(), svdb_f, false);
			fCache.setLastModified(path.getFilePath(), 
					fFileSystemProvider.getLastModifiedTime(
							path.getFilePath()), false);
			if (fDebugEn) {
				fLog.debug("Setting markers (1) for " + path.getFilePath() + " " + markers.size());
			}
			fCache.setMarkers(path.getFilePath(), markers, false);
		}

		fFileSystemProvider.closeStream(in);
		propagateMarkers(path.getFilePath());
		
		cacheDeclarations(svdb_f);
		cacheReferences(svdb_f);
	}

	public synchronized SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	protected SVDBFile processPreProcFile(String path) {
//		SVPreProcScanner sc = new SVPreProcScanner();
		SVPreProcDirectiveScanner sc = new SVPreProcDirectiveScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.setObserver(ob);

		fLog.debug("processPreProcFile: path=" + path);
		InputStream in = fFileSystemProvider.openStream(path);

		if (in == null) {
			fLog.error(getClass().getName() + ": failed to open \"" + path
					+ "\"");
			return null;
		}

		sc.init(in, path);
//		sc.scan();
		sc.process();

		getFileSystemProvider().closeStream(in);

		SVDBFile file = ob.getFiles().get(0);

		/** TMP
		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		 */

		return file;
	}

	public synchronized SVDBFileTree findFileTree(String path, boolean is_argfile) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path, is_argfile);

		return ft;
	}
	
	/**
	 * incrCreateFileTree()
	 * 
	 * Create
	 * 
	 * @param path
	 * @return
	 */
	protected SVDBFileTree incrCreateFileTree(String path) {
		SVDBFileTree ft = new SVDBFileTree(path);
		
		synchronized (fCache) {
			fCache.setFileTree(path, ft, false);
		}
		
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
	

	
	public Iterable<String> getFileNames(IProgressMonitor monitor) {
		return new Iterable<String>() {
			public Iterator<String> iterator() {
				return fCache.getFileList(false).iterator();
			}
		};
	}

	/**
	 * Add the global declarations from the specified scope to the declaration cache
	 *  
	 * @param filename
	 * @param scope
	 */
	protected void cacheDeclarations(SVDBFile file) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData.getDeclCacheMap();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "cacheDeclarations: " + file.getFilePath());
		}
		
		if (!decl_cache.containsKey(file.getFilePath())) {
			decl_cache.put(file.getFilePath(), new ArrayList<SVDBDeclCacheItem>());
		} else {
			decl_cache.get(file.getFilePath()).clear();
		}
	
		// Check to see if we need to cache declarations from this file
		// in a package cache item
		Tuple<String, List<String>> t = null;
		synchronized (fDeferredPkgCacheFiles) {
			for (Tuple<String, List<String>> tp : fDeferredPkgCacheFiles) {
				if (tp.first().equals(file.getFilePath())) {
					t = tp;
					break;
				}
			}
		}

		if (t != null) {
			synchronized (fDeferredPkgCacheFiles) {
				fDeferredPkgCacheFiles.remove(t);
			}
			
			for (String pkgname : t.second()) {
				Map<String, List<SVDBDeclCacheItem>> pkg_map = fIndexCacheData.getPackageCacheMap();
				List<SVDBDeclCacheItem> pkgitem_list = pkg_map.get(pkgname);
				Set<String> processed_files = new HashSet<String>();

				if (fDebugEn) {
					fLog.debug("Caching package " + pkgname + 
							" content from deferred file \"" + file.getFilePath() + "\"");
				}
				cachePkgDeclIncFile(processed_files, pkgname, pkgitem_list, file.getFilePath());
			}
		}
		
		Set<String> processed_files = new HashSet<String>();
		processed_files.add(file.getFilePath());
		
		cacheDeclarations(
				processed_files,
				file.getFilePath(), 
				decl_cache.get(file.getFilePath()),
				null,
				null,
				file,
				false);
	
		SVDBFileTree ft = findFileTree(file.getFilePath(), false);
		if (ft != null) {
			cacheDeclarations(
					processed_files,
					file.getFilePath(), 
					decl_cache.get(file.getFilePath()),
					null, 
					null, 
					ft.getSVDBFile(),
					true);
		}
	}

	/**
	 * Process the FileTree of a package to locate 
	 * include files
	 */
	private void cachePkgDeclFileTree(
			ISVDBChildParent			scope,
			List<SVDBDeclCacheItem>		pkgitem_list,
			SVDBPackageDecl				pkg) {
		int			pkg_start = (pkg.getLocation() != null)?pkg.getLocation().getLine():0;
		int			pkg_end = (pkg.getEndLocation() != null)?pkg.getEndLocation().getLine():-1;
		Set<String>	processed_files = new HashSet<String>();
		
		fLog.debug("--> cachePkgDeclFileTree: " + pkg.getName() + " " +
				pkg_start + ".." + pkg_end);
		
		for (ISVDBChildItem item : scope.getChildren()) {
			int line = (item.getLocation() != null)?(item.getLocation().getLine()):-1;
			if (fDebugEn) {
				fLog.debug("cachePkgDeclFileTree: process " + item.getType() + " @ " +
						line + " (package bounds " + pkg_start + ".." + pkg_end + ")");
			}
			
			if (item.getType().equals(SVDBItemType.Include) && 
					line >= pkg_start && line <= pkg_end) {
				// First, find the pre-processor file corresponding to this include
				cachePkgDeclIncFile(processed_files, pkg.getName(), pkgitem_list, 
						((SVDBInclude)item).getName());

				
			} else if (item instanceof ISVDBChildParent) {
				// Search the sub-scope
				cachePkgDeclFileTree((ISVDBChildParent)item, pkgitem_list, pkg);
			}
		}
		fLog.debug("<-- cachePkgDeclFileTree: " + pkg.getName() + " " +
				pkg_start + ".." + pkg_end);
	}
	
	private void cachePkgDeclIncFile(
			Set<String>					processed_files,
			String						pkgname,
			List<SVDBDeclCacheItem>		pkgitem_list,
			String						inc) {
		if (fDebugEn) {
			fLog.debug("Cache included file \"" + inc + "\"");
		}
		SVDBFile abs_pp_file = fCache.getPreProcFile(new NullProgressMonitor(), inc);
		
		if (abs_pp_file != null) {
			if (fDebugEn) { fLog.debug("File path is absolute"); }
			
		} else {
			if (fDebugEn) { fLog.debug("Searching for relative path"); }
			
			SVDBSearchResult<SVDBFile> r = findIncludedFile(inc);
			if (r != null) {
				abs_pp_file = r.getItem();
			}
		}
		
		if (abs_pp_file != null) {
			// Found something
			if (fDebugEn) { fLog.debug("Included file already parsed: " + abs_pp_file.getFilePath()); }
			
			SVDBFile file = fCache.getFile(new NullProgressMonitor(), abs_pp_file.getFilePath());
			if (file != null) {
				// Add the contents of the target file to the package
				fLog.debug("Calling cacheDeclarations: pkgname=" + pkgname);
				if (!processed_files.contains(file.getFilePath())) {
					processed_files.add(file.getFilePath());
					cacheDeclarations(processed_files, file.getFilePath(), 
							null, pkgname, pkgitem_list, file, false);
					// Now, get the file tree and add sub-included files
					SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), abs_pp_file.getFilePath(), false);
					SVDBFile pp_file = ft.getSVDBFile();
					synchronized (pp_file) {
						for (ISVDBChildItem item : pp_file.getChildren()) {
							if (item.getType() == SVDBItemType.Include) {
								cachePkgDeclIncFile(processed_files, pkgname, pkgitem_list, 
										((SVDBInclude)item).getName());
							}
						}
					}
				} else {
					if (fDebugEn) { fLog.debug("File " + file.getFilePath() + " already processed"); }
				}
			} else {
				// File probably hasn't been parsed yet
				fLog.debug("Deferring caching of file \"" + abs_pp_file.getFilePath() + "\"");
				Tuple<String, List<String>> t = null;
			
				synchronized (fDeferredPkgCacheFiles) {
					for (Tuple<String, List<String>> tp : fDeferredPkgCacheFiles) {
						if (tp.first().equals(abs_pp_file.getFilePath())) {
							t = tp;
							break;
						}
					}
				}
				
				if (t == null) {
					t = new Tuple<String, List<String>>(abs_pp_file.getFilePath(), new ArrayList<String>());
					fDeferredPkgCacheFiles.add(t);
				}
				
				if (!t.second().contains(pkgname)) {
					t.second().add(pkgname);
				}
			}
		} else {
			fLog.debug("Failed to find include file \"" + inc + "\"");
		}		
	}
	
	private void cacheDeclarations(
			Set<String>					processed_files,
			String 						filename,
			List<SVDBDeclCacheItem>		decl_list,
			String						pkgname,
			List<SVDBDeclCacheItem>		pkgitem_list,
			ISVDBChildParent 			scope,
			boolean						is_ft) {
		if (fDebugEn) {
			fLog.debug("--> cacheDeclarations(file=" + filename + ", pkg=" + pkgname + ", " + scope);
		}
		
		for (ISVDBChildItem item : scope.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + item.getType() + " " + SVDBItem.getName(item));
			}
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				SVDBPackageDecl pkg = (SVDBPackageDecl)item;
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename, 
							pkg.getName(), item.getType(), is_ft));
				}
				Map<String, List<SVDBDeclCacheItem>> pkg_map = fIndexCacheData.getPackageCacheMap();
				
				if (pkg_map.containsKey(pkg.getName())) {
					pkg_map.get(pkg.getName()).clear();
				} else {
					pkg_map.put(pkg.getName(), new ArrayList<SVDBDeclCacheItem>());
				}
				
				// Search the FileTree to find files included within the package
				if (!is_ft) {
					SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), filename, false);
					if (ft != null) {
						cachePkgDeclFileTree(ft.getSVDBFile(), pkg_map.get(pkg.getName()), pkg);
					} else {
						fLog.error("Failed to locate FileTree for \"" + filename + "\"");
					}
				}
			
				// Now, proceed looking for explicitly-included content
				cacheDeclarations(processed_files, filename, decl_list, 
						pkg.getName(), pkg_map.get(pkg.getName()), pkg, false);
			} else if (item.getType().isElemOf(SVDBItemType.Function, SVDBItemType.Task,
					SVDBItemType.ClassDecl, SVDBItemType.ModuleDecl, 
					SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl)) {
				fLog.debug(LEVEL_MID, "Adding " + item.getType() + " " + ((ISVDBNamedItem)item).getName() + " to cache");
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename, 
							((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
				}
			
				// Add the declarations to the package cache as well
				if (pkgname != null) {
					if (fDebugEn) {
						fLog.debug("Adding " + SVDBItem.getName(item) + " to package cache \"" + pkgname + "\"");
					}
					pkgitem_list.add(new SVDBDeclCacheItem(this, filename,
						((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
				} else {
					fLog.debug("pkgname is null");
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt decl = (SVDBVarDeclStmt)item;
				
				for (ISVDBChildItem ci : decl.getChildren()) {
					SVDBVarDeclItem di = (SVDBVarDeclItem)ci;
					fLog.debug(LEVEL_MID, "Adding var declaration: " + di.getName());
					
					if (decl_list != null) {
						decl_list.add(new SVDBDeclCacheItem(this, filename, 
							di.getName(), SVDBItemType.VarDeclItem, is_ft));
					}
				}
			} else if (item.getType() == SVDBItemType.TypedefStmt) {
				// Add entries for the typedef
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, filename, 
							((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
				}
				
				// Add the declarations to the package cache as well
				if (pkgname != null) {
					pkgitem_list.add(new SVDBDeclCacheItem(this, filename,
						((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
				}
				
				SVDBTypedefStmt td = (SVDBTypedefStmt)item;
				if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					// Add entries for all enumerators
					SVDBTypeInfoEnum e = (SVDBTypeInfoEnum)td.getTypeInfo();
					fLog.debug("Adding enum " + e.getName() + " to cache");
					for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
						fLog.debug("Adding enumerator " + en.getName() + " to cache");
						if (decl_list != null) {
							decl_list.add(new SVDBDeclCacheItem(this, filename, 
									((ISVDBNamedItem)en).getName(), en.getType(), is_ft));
						}
						// Add the declarations to the package cache as well
						if (pkgname != null) {
							pkgitem_list.add(new SVDBDeclCacheItem(this, filename,
									((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
						}
					}
				}
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				cacheDeclarations(processed_files, filename, decl_list, 
						pkgname, pkgitem_list, (SVDBPreProcCond)item, is_ft);
			} else if (item.getType() == SVDBItemType.MacroDef) {
				if (decl_list != null) {
					fLog.debug(LEVEL_MID, "Add macro declaration \"" + SVDBItem.getName(item) + "\"");
					decl_list.add(new SVDBDeclCacheItem(this, filename, 
							((ISVDBNamedItem)item).getName(), item.getType(), is_ft));
				}
			}
		}
		
		if (fDebugEn) {
			fLog.debug("<-- cacheDeclarations(" + filename + ", " + pkgname + ", " + scope);
		}	
	}
	
	protected void cacheReferences(SVDBFile file) {
		SVDBFileRefCollector collector = new SVDBFileRefCollector();
		collector.visitFile(file);
		
		Map<String, SVDBRefCacheEntry> ref_map = getCacheData().getReferenceCacheMap();
		if (ref_map.containsKey(file.getFilePath())) {
			ref_map.remove(file.getFilePath());
		}
		SVDBRefCacheEntry ref = collector.getReferences();
		ref.setFilename(file.getFilePath());
		ref_map.put(file.getFilePath(), ref);
	}

	public List<SVDBDeclCacheItem> findPackageDecl(
			IProgressMonitor	monitor,
			SVDBDeclCacheItem 	pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> pkg_cache = fIndexCacheData.getPackageCacheMap();
		
		ensureIndexState(monitor, IndexState_AllFilesParsed);
		
		List<SVDBDeclCacheItem> pkg_content = pkg_cache.get(pkg_item.getName());
		
		if (pkg_content != null) {
			ret.addAll(pkg_content);
		}
		
		return ret;
	}
	
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor		monitor,
			String 					name,
			ISVDBFindNameMatcher	matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData.getDeclCacheMap();
		ensureIndexState(monitor, IndexState_AllFilesParsed);
		
		for (Entry<String, List<SVDBDeclCacheItem>> e : decl_cache.entrySet()) {
			for (SVDBDeclCacheItem item : e.getValue()) {
				if (matcher.match(item, name)) {
					ret.add(item);
				}
			}
		}
		
		return ret;
	}
	
	public List<SVDBRefCacheItem> findReferences(IProgressMonitor monitor, String name, ISVDBRefMatcher matcher) {
		List<SVDBRefCacheItem> ret = new ArrayList<SVDBRefCacheItem>();
		
		ensureIndexState(monitor, IndexState_AllFilesParsed);
	
		Map<String, SVDBRefCacheEntry> ref_cache = fIndexCacheData.getReferenceCacheMap();
		for (Entry<String, SVDBRefCacheEntry> e : ref_cache.entrySet()) {
			matcher.find_matches(ret, e.getValue(), name);
		}
		
		for (SVDBRefCacheItem item : ret) {
			item.setRefFinder(this);
		}
		
		return ret;
	}
	
	public List<SVDBRefItem> findReferences(IProgressMonitor monitor, SVDBRefCacheItem item) {
		ensureIndexState(monitor, IndexState_AllFilesParsed);
		
		SVDBRefFinder finder = new SVDBRefFinder(item.getRefType(), item.getRefName());
	
		SVDBFile file = findFile(item.getFilename());
		
		return finder.find_refs(file);
	}
	
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		ensureIndexState(monitor, IndexState_AllFilesParsed);
		
		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the file
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
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		monitor.beginTask("getDeclFilePP", 2);		// ensure state index + findfile/FindTree
		ensureIndexState(new SubProgressMonitor(monitor, 1), IndexState_AllFilesParsed);
		
		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(item.getFilename(), false);
			monitor.worked(1);
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			file = findFile(new SubProgressMonitor(monitor, 1),  item.getFilename());
		}
		monitor.done();
		return file;
	}
	
	public SVPreProcessor createPreProcScanner(String path) {
		
		path = SVFileUtils.normalize(path);
		fLog.debug("--> createPreProcScanner " + path);
		
		ensureIndexState(new NullProgressMonitor(), IndexState_AllFilesParsed);
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path, false);

		if (ft == null) {
			// Map<String, SVDBFileTree> m = getFileTreeMap(new
			// NullProgressMonitor());
			fLog.error("Failed to find pre-proc file for \"" + path + "\"");
			/*
			 * fLog.debug("map.size=" + m.size()); for (String p : m.keySet()) {
			 * fLog.debug("    " + p); }
			 */
			fLog.debug("<-- createPreProcScanner " + path + " null");
			return null;
		}

		InputStream in = getFileSystemProvider().openStream(path);
		IPreProcMacroProvider mp = createMacroProvider(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);

		SVPreProcessor pp = new SVPreProcessor(in, path, dp);

		fLog.debug("<-- createPreProcScanner " + path);
		return pp;
	}

}
