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

import java.io.BufferedInputStream;
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
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.SubProgressMonitor;

public abstract class AbstractSVDBIndex implements ISVDBIndex,
		ISVDBFileSystemChangeListener, ILogLevelListener, ILogLevel {
	private static final int IndexState_AllInvalid = 0;
	private static final int IndexState_RootFilesDiscovered = (IndexState_AllInvalid + 1);
	private static final int IndexState_FilesPreProcessed = (IndexState_RootFilesDiscovered + 1);
	private static final int IndexState_FileTreeValid = (IndexState_FilesPreProcessed + 1);
	private static final int IndexState_AllFilesParsed = (IndexState_FileTreeValid + 1);

	public  String 									fProjectName;
	private String 									fBaseLocation;
	private String 									fResolvedBaseLocation;
	private String 									fBaseLocationDir;

	private SVDBBaseIndexCacheData 					fIndexCacheData;
	private boolean								fCacheDataValid;
	
	protected Set<String>							fMissingIncludes;

	private ISVDBIncludeFileProvider 				fIncludeFileProvider;

	private List<ISVDBIndexChangeListener>			fIndexChageListeners;

	protected static Pattern 						fWinPathPattern;
	protected LogHandle 							fLog;
	private ISVDBFileSystemProvider 				fFileSystemProvider;

	protected boolean 							fLoadUpToDate;
	private ISVDBIndexCache 						fCache;
	private Map<String, Object> 					fConfig;
	
	// Manages a list of the directories that managed files are stored in
	private Set<String>								fFileDirs;
	
	// Controls indexing parallelism
	private int									fMaxIndexThreads = 0;
	protected boolean								fDebugEn;

	protected boolean								fInWorkspaceOk;

//	private Map<String, List<SVDBDeclCacheItem>>	fPackageCacheMap;
//	private ISVEditorJob							fEnsureIndexStateJob;

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
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
//		fPackageCacheMap = new HashMap<String, List<SVDBDeclCacheItem>>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle(getLogName());
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fMissingIncludes = new HashSet<String>();
		fMaxIndexThreads = SVCorePlugin.getMaxIndexThreads();
		fAutoRebuildEn = true;
		
		fFileDirs = new HashSet<String>();
	}

	public AbstractSVDBIndex(String project, String base_location,
			ISVDBFileSystemProvider fs_provider, ISVDBIndexCache cache,
			Map<String, Object> config) {
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
	protected boolean checkCacheValid() {
		boolean valid = true;
		String version = SVCorePlugin.getDefault().getVersion();
		
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
			/*
			 * TEMP: if
			 * (fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
			 * Map<String, String> define_map = (Map<String, String>)
			 * fConfig.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
			 * 
			 * for (String key : define_map.keySet()) { if
			 * (!fIndexCacheData.getGlobalDefines().containsKey(key) ||
			 * !fIndexCacheData
			 * .getGlobalDefines().get(key).equals(define_map.get(key))) { valid
			 * = false; break; } } }
			 */
		}

		if (fCache.getFileList().size() > 0) {
			for (String path : fCache.getFileList()) {
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
		fCacheDataValid = fCache.init(m, fIndexCacheData);

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
						i.init(e.getKey(), this);
					}
				}
			}
			
			// Register all files with the directory set
			for (String f : fCache.getFileList()) {
				addFileDir(f);
			}
		} else {
			if (fDebugEn) {
				fLog.debug("Cache " + getBaseLocation() + " is invalid");
			}
			invalidateIndex("Cache is invalid", true);
		}
		// set the version to check later
		fIndexCacheData.setVersion(SVCorePlugin.getDefault().getVersion());

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
	
	public void loadIndex(IProgressMonitor monitor) {
		ensureIndexState(monitor, IndexState_AllFilesParsed);
	}

	/**
	 * @param monitor
	 * @param state
	 */
	public synchronized void ensureIndexState(IProgressMonitor monitor, int state) {
		monitor.beginTask("Ensure Index State for " + getBaseLocation(), 4);
		if (fIndexState < IndexState_RootFilesDiscovered
				&& state >= IndexState_RootFilesDiscovered) {
			if (fDebugEn) {
				fLog.debug("Moving index to state RootFilesDiscovered from "
						+ fIndexState);
			}
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			discoverRootFiles(m);
			// Flush file-list back to backing store
			fCache.sync();
			fIndexState = IndexState_RootFilesDiscovered;
			fIsDirty = false;
		}
		if (fIndexState < IndexState_FilesPreProcessed
				&& state >= IndexState_FilesPreProcessed) {
			if (fDebugEn) {
				fLog.debug("Moving index to state FilesPreProcessed from "
						+ fIndexState);
			}
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			preProcessFiles(m);
			fIndexState = IndexState_FilesPreProcessed;
			fIsDirty = false;
		}
		if (fIndexState < IndexState_FileTreeValid
				&& state >= IndexState_FileTreeValid) {
			if (fDebugEn) {
				fLog.debug("Moving index to state FileTreeValid from "
						+ fIndexState);
			}
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			buildFileTree(m);
			fIndexState = IndexState_FileTreeValid;
			
			propagateAllMarkers();
			notifyIndexRebuilt();
			fIsDirty = false;
		}
		if (fIndexState < IndexState_AllFilesParsed
				&& state >= IndexState_AllFilesParsed) {
			if (fCacheDataValid) {
				SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
				fCache.initLoad(m);
				m.done();
			} else {
				parseFiles(monitor);
			}
			fIndexState = IndexState_AllFilesParsed;
			fIsDirty = false;
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
		synchronized (fCache) {
			paths.addAll(fCache.getFileList());
		}
		final SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
		m.beginTask("Parsing Files", paths.size());
		
		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			parseFilesJob(paths, m);
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						parseFilesJob(paths, m);
					}
				}, "parse_" + getBaseLocation() + "_" + i);
				threads[i].setPriority(Thread.MAX_PRIORITY);
				threads[i].start();
			}
			
			// Now, wait for the threads to complete
			join_threads(threads);
		}
		
		m.done();
	}

	protected void parseFilesJob(List<String> paths, IProgressMonitor monitor) {
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
					ft_root = fCache.getFileTree(new NullProgressMonitor(), path);
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
				IPreProcMacroProvider mp = createMacroProvider(ft_root);
				processFile(ft_root, mp);
				
				synchronized (fCache) {
					ret = fCache.getFile(new NullProgressMonitor(), path);
				}
			}

			synchronized(monitor) {
				monitor.worked(1);
			}
		}
	}

	protected void invalidateIndex(String reason, boolean force) {
		if (fDebugEn) {
			if (fAutoRebuildEn || force) {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: " +
						((reason == null)?"No reason given":reason));
			} else {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: " +
						((reason == null)?"No reason given":reason) + 
						" (ignored -- AutoRebuild disabled)");
			}
		}
		
		if (fAutoRebuildEn || force) {
			fIndexState = IndexState_AllInvalid;
			fCacheDataValid = false;
			fIndexCacheData.clear();
			fCache.clear();
			fMissingIncludes.clear();
		} else {
			fIsDirty = true;
		}

//		fPackageCacheMap = new HashMap<String, List<SVDBDeclCacheItem>>();
	}

	public void rebuildIndex() {
		invalidateIndex("Rebuild Index Requested", true);
	}

	public ISVDBIndexCache getCache() {
		return fCache;
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
			if (fCache.getFileList().contains(path)) {
//				invalidateIndex();
				if (fDebugEn) {
					fLog.debug(LEVEL_MIN, "fileChanged: " + path);
				}
				fCache.setFile(path, null);
				fCache.setLastModified(path, 
						getFileSystemProvider().getLastModifiedTime(path));
			}
		}
	}

	public void fileRemoved(String path) {
		synchronized (fCache) {
			if (fCache.getFileList().contains(path)) {
				invalidateIndex("File Removed", false);
			}
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
			invalidateIndex("File Added", false);
		}
	}

	public String getBaseLocation() {
		return fBaseLocation;
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
			rebuildIndex();
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
	public Set<String> getFileList(IProgressMonitor monitor) {
		ensureIndexState(monitor, IndexState_FileTreeValid);
		return fCache.getFileList();
	}
	
	public synchronized List<SVDBMarker> getMarkers(String path) {
		/*SVDBFile file = */findFile(path);
		
		return fCache.getMarkers(path);
	}

	protected void addFile(String path) {
		synchronized (fCache) {
			fCache.addFile(path);
			fCache.setLastModified(path, getFileSystemProvider().getLastModifiedTime(path));
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
		fCache.clear();
		fFileDirs.clear();
	}

	protected void propagateAllMarkers() {
		Set<String> file_list = fCache.getFileList();
		for (String path : file_list) {
			if (path != null) {
				propagateMarkers(path);
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
		synchronized (fCache) {
			paths.addAll(fCache.getFileList());
		}
		
		monitor.beginTask("Pre-Process Files", paths.size());

		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			preProcessFilesJob(paths, monitor);
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						preProcessFilesJob(paths, monitor);
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
			
			SubProgressMonitor m = null;
			synchronized(monitor) {
				m = new SubProgressMonitor(monitor, 1);
				m.beginTask("Process " + path, 1);
			}
			
			SVDBFile file = processPreProcFile(path);
			synchronized (fCache) {
				fCache.setPreProcFile(path, file);
				fCache.setLastModified(path, 
						fFileSystemProvider.getLastModifiedTime(path));
			}
			
			synchronized(monitor) {
				m.done();
			}
		}
	}

	protected void buildFileTree(final IProgressMonitor monitor) {
		final List<String> paths = new ArrayList<String>(); 
		paths.addAll(getCache().getFileList());
		final List<String> missing_includes = new ArrayList<String>();
		
		monitor.beginTask("Building File Tree", paths.size());

		// Decide how many threads to spawn.
		// Want each thread to work on at least 16 files
		int num_threads = Math.min(fMaxIndexThreads, paths.size()/16);
		if (fMaxIndexThreads <= 1 || num_threads <= 1) {
			// only a single thread
			buildFileTreeJob(paths, missing_includes, monitor);
		} else {
			Thread threads[] = new Thread[num_threads];
			for (int i=0; i<threads.length; i++) {
				threads[i] = new Thread(new Runnable() {
					
					public void run() {
						buildFileTreeJob(paths, missing_includes, monitor);
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
				if (fCache.getFileTree(new NullProgressMonitor(), path) != null) {
					continue;
				}
			}
			
			SVDBFile pp_file ;

			synchronized (fCache) {
				pp_file = fCache.getPreProcFile(
						new NullProgressMonitor(), path);
				
			}
				
			if (pp_file == null) {
				fLog.error("Failed to get pp_file \"" + path + "\" from cache");
			}
				
			SVDBFileTree ft_root = new SVDBFileTree( (SVDBFile) pp_file.duplicate());
				Set<String> included_files = new HashSet<String>();
				Map<String, SVDBFileTree> working_set = new HashMap<String, SVDBFileTree>();
				buildPreProcFileMap(null, ft_root, missing_includes, included_files, working_set);
		}
	}

	private void buildPreProcFileMap(
			SVDBFileTree 				parent, 
			SVDBFileTree 				root,
			List<String>				missing_includes,
			Set<String>					included_files,
			Map<String, SVDBFileTree>	working_set) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();

		if (fDebugEn) {
			fLog.debug("setFileTree " + root.getFilePath());
		}
		if (!working_set.containsKey(root.getFilePath())) {
			working_set.put(root.getFilePath(), root);
		}
//		/** TMP
		synchronized (fCache) {
			if (!working_set.containsKey(root.getFilePath())) {
				System.out.println("FileTree " + root.getFilePath() + " not in working set");
			}
			fCache.setFileTree(root.getFilePath(), root);
		}
//		 */

		if (parent != null) {
			root.getIncludedByFiles().add(parent.getFilePath());
		}

		synchronized (root) {
			ft_utils.resolveConditionals(root, new SVPreProcDefineProvider(
					createPreProcMacroProvider(root, working_set)));
		}

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		included_files.add(root.getFilePath());
		addPreProcFileIncludeFiles(root, root.getSVDBFile(), markers, 
				missing_includes, included_files, working_set);

		synchronized (fCache) {
			fCache.setFileTree(root.getFilePath(), root);
			fCache.setMarkers(root.getFilePath(), markers);
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
						buildPreProcFileMap(root, ft, missing_includes, included_files, working_set);
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
		if (fDebugEn) {
			fLog.debug("findIncludedFile: " + path);
		}
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = resolvePath(inc_dir + "/" + path, fInWorkspaceOk);
			SVDBFile file = null;

			if (fDebugEn) {
				fLog.debug("Include Path: \"" + inc_path + "\"");
			}

			if ((file = fCache.getPreProcFile(new NullProgressMonitor(),
					inc_path)) != null) {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: \"" + inc_path
							+ "\" already in map");
				}
			} else {
				if (fFileSystemProvider.fileExists(inc_path)) {
					if (fDebugEn) {
						fLog.debug("findIncludedFile: building entry for \""
								+ inc_path + "\"");
					}

					file = processPreProcFile(inc_path);
					addFile(inc_path);
					fCache.setPreProcFile(inc_path, file);
					fCache.setLastModified(inc_path, 
							fFileSystemProvider.getLastModifiedTime(inc_path));
				} else {
					if (fDebugEn) {
						fLog.debug("findIncludedFile: file \"" + inc_path
								+ "\" does not exist");
					}
				}
			}

			if (file != null) {
				return new SVDBSearchResult<SVDBFile>(file, this);
			}
		}

		String res_path = resolvePath(path, fInWorkspaceOk);

		if (fFileSystemProvider.fileExists(res_path)) {
			SVDBFile pp_file = null;
			if ((pp_file = processPreProcFile(res_path)) != null) {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: adding file \"" + path + "\"");
				}
				addFile(res_path);
				return new SVDBSearchResult<SVDBFile>(pp_file, this);
			}
		}

		return null;
	}

	protected String resolvePath(String path_orig, boolean in_workspace_ok) {
		String path = path_orig;
		String norm_path = null;

		if (fDebugEn) {
			fLog.debug("resolvePath: " + path_orig);
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
			IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = ws_root.getFileForLocation(new Path(norm_path));
			if (file != null && file.exists()) {
				norm_path = "${workspace_loc}" + file.getFullPath().toOSString();
			}
		}

		return (norm_path != null) ? norm_path : path_orig;
	}

	private String resolveRelativePath(String base, String path) {
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base + "/" + path);

		if (fDebugEn) {
			fLog.debug("    Checking normalizedPath: " + norm_path
					+ " ; ResolvedBaseLocation: " + getResolvedBaseLocationDir());
		}

		if (fFileSystemProvider.fileExists(norm_path)) {
			return norm_path;
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
				fLog.debug("base_dir=" + base_dir);
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					File path_f_t = new File(base_dir_p.toFile(), path);
					try {
						if (path_f_t.exists()) {
							if (fDebugEn) {
								fLog.debug("Path does exist outside the project: "
										+ path_f_t.getCanonicalPath());
							}
							norm_path = SVFileUtils.normalize(path_f_t
									.getCanonicalPath());
							return norm_path;
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}

		return null;
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
		fIndexChageListeners.add(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.remove(l);
	}

	protected void notifyIndexRebuilt() {
		for (ISVDBIndexChangeListener l : fIndexChageListeners) {
			l.index_rebuilt();
		}
	}

	public boolean isLoaded() {
		/**
		 * return (fIndexFileMapValid && fPreProcFileMapValid);
		 */
		return true; // deprecated
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

	public SVDBFile parse(
			IProgressMonitor	monitor, 
			InputStream 		in,
			String 				path, 
			List<SVDBMarker>	markers) {
		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(null);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);

		path = SVFileUtils.normalize(path);

		SVDBFileTree file_tree = findFileTree(path);

		if (file_tree == null) {
			if (getFileSystemProvider().fileExists(path)) {
				// If the file does exist, but isn't included in the
				// list of discovered files, invalidate the index,
				// add the file, and try again
				invalidateIndex("Failed to find FileTree for " + path, false);
				addFile(path);
				file_tree = findFileTree(path);
				
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
		
		markers.clear();
		List<SVDBMarker> markers_e = fCache.getMarkers(path); 
		if (markers_e != null) {
			for (SVDBMarker m : markers_e) {
				if (m.getKind() == MarkerKind.MissingInclude) {
					markers.add(m);
				}
			}
		}

		InputStreamCopier copier = new InputStreamCopier(in);
		in = null;

		SVPreProcScanner sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();
		sc.setObserver(ob);

		file_tree = file_tree.duplicate();

		sc.init(copier.copy(), path);
		sc.scan();

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
		System.out.println("file path: " + path + " is " + svdb_f.getFilePath());
		/** TMP:
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		 */

		// propagateMarkersPreProc2DB(file_tree, svdb_pp, svdb_f);
		// addMarkers(path, svdb_f);

		return svdb_f;
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public SVDBFile findFile(String path) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);

		SVDBFile ret;

		synchronized (fCache) {
			ret = fCache.getFile(new NullProgressMonitor(), path);
		}

		if (ret == null) {
			SVDBFileTree ft_root;
			synchronized (fCache) {
				ft_root = fCache.getFileTree(new NullProgressMonitor(), path);
			}

			if (ft_root != null) {
				IPreProcMacroProvider mp = createMacroProvider(ft_root);
				processFile(ft_root, mp);
				
				synchronized (fCache) {
					ret = fCache.getFile(new NullProgressMonitor(), path);
				}
			} else {
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.error("File Path \"" + path + "\" not in index", e);
					for (String p : getFileList(new NullProgressMonitor())) {
						System.out.println("path: " + p);
					}
				}
			}
		}

		if (ret == null) {
			try {
				throw new Exception("File \"" + path + "\" not found");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		return ret;
	}

	protected void processFile(SVDBFileTree path, IPreProcMacroProvider mp) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);

		String path_s = path.getFilePath();

		InputStream in = fFileSystemProvider.openStream(path_s);

		if (in == null) {
			fLog.error("ProcessFile: Failed to open file \"" + path_s + "\"");
		}

		BufferedInputStream in_b = new BufferedInputStream(in);

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

		SVDBFile svdb_f = factory.parse(in_b, path.getFilePath(), markers);

		// Problem parsing the file..
		if (svdb_f == null) {
			return;
		}
		
		cacheDeclarations(svdb_f);

		/** TMP:
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path
				.getFilePath()));
		 */

		fFileSystemProvider.clearMarkers(path_s);

		fCache.setFile(path.getFilePath(), svdb_f);
		fCache.setLastModified(path.getFilePath(), 
				fFileSystemProvider.getLastModifiedTime(
						path.getFilePath()));
		fCache.setMarkers(path.getFilePath(), markers);

		fFileSystemProvider.closeStream(in);
		propagateMarkers(path.getFilePath());
	}

	public synchronized SVDBFile findPreProcFile(String path) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);
		return fCache.getPreProcFile(new NullProgressMonitor(), path);
	}

	protected SVDBFile processPreProcFile(String path) {
		SVPreProcScanner sc = new SVPreProcScanner();
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
		sc.scan();

		getFileSystemProvider().closeStream(in);

		SVDBFile file = ob.getFiles().get(0);

		/** TMP
		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		 */

		return file;
	}

	public synchronized SVDBFileTree findFileTree(String path) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path);

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
			fCache.setFileTree(path, ft);
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
	
	public Iterable<String> getFileNames(IProgressMonitor monitor) {
		return new Iterable<String>() {
			public Iterator<String> iterator() {
				return fCache.getFileList().iterator();
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
		
		cacheDeclarations(file.getFilePath(), file);
	}
	
	private void cacheDeclarations(String filename, ISVDBChildParent scope) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData.getDeclCacheMap();
		
		for (ISVDBChildItem item : scope.getChildren()) {
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				decl_cache.get(filename).add(new SVDBDeclCacheItem(this, filename, 
						((SVDBPackageDecl)item).getName(), item.getType()));
				cacheDeclarations(filename, (SVDBPackageDecl)item);
			} else if (item.getType().isElemOf(SVDBItemType.Function, SVDBItemType.Task,
					SVDBItemType.ClassDecl, SVDBItemType.ModuleDecl, 
					SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl, 
					SVDBItemType.TypedefStmt)) {
				fLog.debug("Adding " + item.getType() + " " + ((ISVDBNamedItem)item).getName() + " to cache");
				decl_cache.get(filename).add(new SVDBDeclCacheItem(this, filename, 
						((ISVDBNamedItem)item).getName(), item.getType()));
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				cacheDeclarations(filename, (SVDBPreProcCond)item);
			} else if (item.getType() == SVDBItemType.MacroDef) {
				decl_cache.get(filename).add(new SVDBDeclCacheItem(this, filename, 
						((ISVDBNamedItem)item).getName(), item.getType()));
			}
		}
	}

	/*
	private void cachePreProcDeclarations(String filename, ISVDBChildParent scope) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = fIndexCacheData.getDeclCacheMap();
		
		for (ISVDBChildItem item : scope.getChildren()) {
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				cachePreProcDeclarations(filename, (SVDBPackageDecl)item);
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				SVDBPreProcCond c = (SVDBPreProcCond)item;
				cachePreProcDeclarations(filename, c);
			} else if (item.getType().isElemOf(SVDBItemType.MacroDef)) {
				fLog.debug("Adding " + item.getType() + " " + ((ISVDBNamedItem)item).getName() + " to cache");
				decl_cache.get(filename).add(new SVDBDeclCacheItem(this, filename, 
						((ISVDBNamedItem)item).getName(), item.getType()));
			}
		}
	}
	 */

	public List<SVDBDeclCacheItem> findPackageDecl(
			IProgressMonitor	monitor,
			SVDBDeclCacheItem 	pkg_item) {
		// TODO Auto-generated method stub
		return null;
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		ensureIndexState(monitor, IndexState_AllFilesParsed);
		
		return findFile(item.getFilename());
	}

	public SVPreProcScanner createPreProcScanner(String path) {
		path = SVFileUtils.normalize(path);
		InputStream in = getFileSystemProvider().openStream(path);
		SVDBFileTree ft = findFileTree(path);

		if (ft == null) {
			// Map<String, SVDBFileTree> m = getFileTreeMap(new
			// NullProgressMonitor());
			fLog.error("Failed to find pre-proc file for \"" + path + "\"");
			/*
			 * fLog.debug("map.size=" + m.size()); for (String p : m.keySet()) {
			 * fLog.debug("    " + p); }
			 */
			return null;
		}

		IPreProcMacroProvider mp = createMacroProvider(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);

		SVPreProcScanner pp = new SVPreProcScanner();
		pp.setDefineProvider(dp);

		pp.init(in, path);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(true);

		return pp;
	}

}
