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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Pattern;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
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
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.job_mgr.ISVEditorJob;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.SubProgressMonitor;

public abstract class AbstractSVDBIndex implements ISVDBIndex,
		ISVDBFileSystemChangeListener {
	private static final int IndexState_AllInvalid = 0;
	private static final int IndexState_RootFilesDiscovered = (IndexState_AllInvalid + 1);
	private static final int IndexState_FilesPreProcessed = (IndexState_RootFilesDiscovered + 1);
	private static final int IndexState_FileTreeValid = (IndexState_FilesPreProcessed + 1);
	private static final int IndexState_AllFilesParsed = (IndexState_FileTreeValid + 1);

//	private String fProjectName;
	private String fBaseLocation;
	private String fResolvedBaseLocation;
	private String fBaseLocationDir;

	private SVDBBaseIndexCacheData 			fIndexCacheData;

	private ISVDBIncludeFileProvider 		fIncludeFileProvider;

	private List<ISVDBIndexChangeListener>	fIndexChageListeners;

	protected static Pattern 				fWinPathPattern;
	protected static final List<String> 	fSVExtensions;
	protected static final List<String> 	fIgnoreDirs;
	protected LogHandle 					fLog;
	private ISVDBFileSystemProvider 		fFileSystemProvider;

	protected boolean 						fLoadUpToDate;
	private ISVDBIndexCache 				fCache;
	private Map<String, Object> 			fConfig;
	private ISVEditorJob					fEnsureIndexStateJob;

	/**
	 * True if the root file list is valid.
	 */
	private int fIndexState;

	static {
		fSVExtensions = new ArrayList<String>();

		fSVExtensions.add(".sv");
		fSVExtensions.add(".svh");
		fSVExtensions.add(".v");
		fSVExtensions.add(".V");
		fSVExtensions.add(".vl");
		fSVExtensions.add(".vlog");

		fIgnoreDirs = new ArrayList<String>();
		fIgnoreDirs.add("/.svn/");
		fIgnoreDirs.add("/CVS/");

		fWinPathPattern = Pattern.compile("\\\\");
	}

	protected AbstractSVDBIndex(String project) {
//		fProjectName = project;
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
	}

	public AbstractSVDBIndex(String project, String base_location,
			ISVDBFileSystemProvider fs_provider, ISVDBIndexCache cache,
			Map<String, Object> config) {
		this(project);
		fBaseLocation = base_location;
		fCache = cache;
		fConfig = config;
		fLog = LogFactory.getLogHandle("AbstractSVDBIndex");

		setFileSystemProvider(fs_provider);
	}

	/**
	 * Called when the index is initialized to determine whether the cached
	 * information is still valid
	 * 
	 * @return
	 */
	protected boolean checkCacheValid() {
		boolean valid = true;

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
					
					fLog.debug("Cache " + getBaseLocation() + 
							" is invalid : path " + path + " fs_timestamp="
							+ fs_timestamp + " cache_timestamp=" + cache_timestamp);
					valid = false;
					break;
				}
			}
		} else {
			fLog.debug("Cache " + getBaseLocation() + " is invalid -- 0 entries");
			SVDBIndexFactoryUtils.setBaseProperties(fConfig, this);
			valid = false;
		}
		
		if (getCacheData().getMissingIncludeFiles().size() > 0 && valid) {
			fLog.debug("Checking missing-include list added files");
			for (String path : getCacheData().getMissingIncludeFiles()) {
				SVDBSearchResult<SVDBFile> res = findIncludedFile(path);
				if (res != null) {
					fLog.debug("    Found previously-missing include file \"" + path + "\"");
					valid = false;
					break;
				}
			}
		}
		
		fLog.debug("Cache " + getBaseLocation() + " is " + ((valid)?"valid":"invalid"));

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
		boolean valid = fCache.init(m, fIndexCacheData);

		if (valid) {
			valid = checkCacheValid();
		}

		if (valid) {
			fLog.debug("Cache is valid");
			fIndexState = IndexState_AllFilesParsed;
		} else {
			fLog.debug("Cache " + getBaseLocation() + " is invalid");
			invalidateIndex();
		}

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
		
		if (valid) {
			fCache.initLoad(new SubProgressMonitor(monitor, 1));
		}

		monitor.done();
	}
	
	public synchronized void loadIndex(IProgressMonitor monitor) {
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
			fLog.debug("Moving index to state RootFilesDiscovered from "
					+ fIndexState);
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			discoverRootFiles(m);
			// Flush file-list back to backing store
			fCache.sync();
			fIndexState = IndexState_RootFilesDiscovered;
		}
		if (fIndexState < IndexState_FilesPreProcessed
				&& state >= IndexState_FilesPreProcessed) {
			fLog.debug("Moving index to state FilesPreProcessed from "
					+ fIndexState);
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			preProcessFiles(m);
			fIndexState = IndexState_FilesPreProcessed;
		}
		if (fIndexState < IndexState_FileTreeValid
				&& state >= IndexState_FileTreeValid) {
			fLog.debug("Moving index to state FileTreeValid from "
					+ fIndexState);
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			buildFileTree(m);
			fIndexState = IndexState_FileTreeValid;
			
			propagateAllMarkers();
			notifyIndexRebuilt();
		}
		if (fIndexState < IndexState_AllFilesParsed
				&& state >= IndexState_AllFilesParsed) {
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			List<String> files = getFileList(new NullProgressMonitor());
			m.beginTask("Parsing Files", files.size());
			for (String f : files) {
				findFile(f);
				m.worked(1);
			}
			m.done();
			fIndexState = IndexState_AllFilesParsed;
		}
		
		monitor.done();
	}

	protected void invalidateIndex() {
		fIndexState = IndexState_AllInvalid;
		fCache.clear();
	}

	public void rebuildIndex() {
		invalidateIndex();
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
		if (getCache().getFileList().contains(path)) {
//			invalidateIndex();
			getCache().setFile(path, null);
			getCache().setLastModified(path, getFileSystemProvider().getLastModifiedTime(path));
		}
	}

	public void fileRemoved(String path) {
		if (getCache().getFileList().contains(path)) {
			invalidateIndex();
		}
	}

	public void fileAdded(String path) {
		// TODO: Not sure what to do with this one
		// Just for safety, invalidate the index when files are added
		fLog.debug("fileAdded: " + path);
		invalidateIndex();
	}

	public String getBaseLocation() {
		return fBaseLocation;
	}

	public String getResolvedBaseLocation() {
		if (fResolvedBaseLocation == null) {
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(fBaseLocation,
					true);
		}

		return fResolvedBaseLocation;
	}

	public String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			String base_location = getResolvedBaseLocation();
			fLog.debug("   base_location: " + base_location);
			if (fFileSystemProvider.isDir(base_location)) {
				fLog.debug("       base_location + " + base_location
						+ " is_dir");
				fBaseLocationDir = base_location;
			} else {
				fLog.debug("       base_location + " + base_location
						+ " not_dir");
				fBaseLocationDir = SVFileUtils.getPathParent(base_location);
				fLog.debug("   getPathParent " + base_location + ": "
						+ fBaseLocationDir);
			}
		}
		return fBaseLocationDir;
	}

	public void setGlobalDefine(String key, String val) {
		fLog.debug("setGlobalDefine(" + key + ", " + val + ")");
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
	public synchronized List<String> getFileList(IProgressMonitor monitor) {
		ensureIndexState(monitor, IndexState_FileTreeValid);
		return fCache.getFileList();
	}
	
	public synchronized List<SVDBMarker> getMarkers(String path) {
		/*SVDBFile file = */findFile(path);
		
		return fCache.getMarkers(path);
	}

	protected void addFile(String path) {
		fCache.addFile(path);
		fCache.setLastModified(path, getFileSystemProvider().getLastModifiedTime(path));
	}

	protected void clearFilesList() {
		fCache.clear();
	}

	protected void propagateAllMarkers() {
		List<String> file_list = fCache.getFileList();
		for (String path : file_list) {
			propagateMarkers(path);
		}
	}
	
	protected void propagateMarkers(String path) {
		List<SVDBMarker> ml = fCache.getMarkers(path);
		getFileSystemProvider().clearMarkers(path);
		
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
	protected void preProcessFiles(IProgressMonitor monitor) {
		List<String> paths = getCache().getFileList();
		monitor.beginTask("Pre-Process Files", paths.size());

		for (int i = 0; i < paths.size(); i++) {
			String path = paths.get(i);
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			m.beginTask("Process " + path, 1);
			SVDBFile file = processPreProcFile(path);
			fCache.setPreProcFile(path, file);
			fCache.setLastModified(path, file.getLastModified());
			m.done();
		}
		monitor.done();
	}

	protected void buildFileTree(IProgressMonitor monitor) {
		List<String> paths = getCache().getFileList();
		List<String> missing_includes = new ArrayList<String>();
		monitor.beginTask("Building File Tree", paths.size());

		for (int i = 0; i < paths.size(); i++) {
			String path = paths.get(i);
			if (fCache.getFileTree(new NullProgressMonitor(), path) == null) {
				SVDBFile pp_file = fCache.getPreProcFile(
						new NullProgressMonitor(), path);
				SVDBFileTree ft_root = new SVDBFileTree(
						(SVDBFile) pp_file.duplicate());
				buildPreProcFileMap(null, ft_root, missing_includes);
			}
		}
		
		getCacheData().clearMissingIncludeFiles();
		for (String path : missing_includes) {
			getCacheData().addMissingIncludeFile(path);
		}

		monitor.done();
	}

	private void buildPreProcFileMap(
			SVDBFileTree 	parent, 
			SVDBFileTree 	root,
			List<String>	missing_includes) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();

		fCache.setFileTree(root.getFilePath(), root);

		if (parent != null) {
			root.getIncludedByFiles().add(parent.getFilePath());
		}

		ft_utils.resolveConditionals(root, new SVPreProcDefineProvider(
				createPreProcMacroProvider(root)));

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		addPreProcFileIncludeFiles(root, root.getSVDBFile(), markers, missing_includes);

		fCache.setFileTree(root.getFilePath(), root);
		fCache.setMarkers(root.getFilePath(), markers);
	}

	private void addPreProcFileIncludeFiles(
			SVDBFileTree 		root,
			ISVDBScopeItem 		scope,
			List<SVDBMarker>	markers,
			List<String>		missing_includes) {
		for (int i = 0; i < scope.getItems().size(); i++) {
			ISVDBItemBase it = scope.getItems().get(i);

			if (it.getType() == SVDBItemType.Include) {
				fLog.debug("Include file: " + ((ISVDBNamedItem) it).getName());

				// Look local first
				SVDBSearchResult<SVDBFile> f = findIncludedFileGlobal(((ISVDBNamedItem) it)
						.getName());

				if (f != null) {
					fLog.debug("Found include file \""
							+ ((ISVDBNamedItem) it).getName()
							+ "\" in index \"" + f.getIndex().getBaseLocation()
							+ "\"");
					String file_path = f.getItem().getFilePath();
					fLog.debug("Adding included file \"" + file_path
							+ " to FileTree \"" + root.getFilePath() + "\"");
					SVDBFileTree ft = new SVDBFileTree((SVDBFile) f.getItem().duplicate());
					root.addIncludedFile(ft.getFilePath());
					fLog.debug("    Now has " + ft.getIncludedFiles().size()
							+ " included files");
					buildPreProcFileMap(root, ft, missing_includes);
				} else {
					String missing_path = ((ISVDBNamedItem) it).getName(); 
					fLog.error("Failed to find include file \""
							+ missing_path + "\" (from file " + root.getFilePath() + ")");
					if (!missing_includes.contains(missing_path)) {
						missing_includes.add(missing_path);
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
				addPreProcFileIncludeFiles(root, (ISVDBScopeItem) it, markers, missing_includes);
			}
		}
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		fLog.debug("findIncludedFile: " + path);
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = resolvePath(inc_dir + "/" + path);
			SVDBFile file = null;

			fLog.debug("Include Path: \"" + inc_path + "\"");

			if ((file = fCache.getPreProcFile(new NullProgressMonitor(),
					inc_path)) != null) {
				fLog.debug("findIncludedFile: \"" + inc_path
						+ "\" already in map");
			} else {
				if (fFileSystemProvider.fileExists(inc_path)) {
					fLog.debug("findIncludedFile: building entry for \""
							+ inc_path + "\"");

					file = processPreProcFile(inc_path);
					addFile(inc_path);
					fCache.setPreProcFile(inc_path, file);
					fCache.setLastModified(inc_path, file.getLastModified());
				} else {
					fLog.debug("findIncludedFile: file \"" + inc_path
							+ "\" does not exist");
				}
			}

			if (file != null) {
				return new SVDBSearchResult<SVDBFile>(file, this);
			}
		}

		String res_path = resolvePath(path);

		if (fFileSystemProvider.fileExists(res_path)) {
			SVDBFile pp_file = null;
			if ((pp_file = processPreProcFile(res_path)) != null) {
				fLog.debug("findIncludedFile: adding file \"" + path + "\"");
				addFile(res_path);
				return new SVDBSearchResult<SVDBFile>(pp_file, this);
			}
		}

		return null;
	}

	protected String resolvePath(String path_orig) {
		String path = path_orig;
		String norm_path = null;

		fLog.debug("resolvePath: " + path_orig);

		// relative to the base location or one of the include paths
		if (path.startsWith("..")) {
			fLog.debug("    path starts with ..");
			if ((norm_path = resolveRelativePath(getResolvedBaseLocationDir(),
					path)) == null) {
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					fLog.debug("    Check: " + inc_path + " ; " + path);
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break;
					}
				}
			} else {
				fLog.debug("norm_path=" + norm_path);
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

		return (norm_path != null) ? norm_path : path_orig;
	}

	private String resolveRelativePath(String base, String path) {
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base + "/" + path);

		fLog.debug("    Checking normalizedPath: " + norm_path
				+ " ; ResolvedBaseLocation: " + getResolvedBaseLocationDir());

		if (fFileSystemProvider.fileExists(norm_path)) {
			return norm_path;
		} else if (getBaseLocation().startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path
			// by computing the absolute path
			String base_loc = getResolvedBaseLocationDir();
			fLog.debug("Possible outside-workspace path: " + base_loc);
			base_loc = base_loc.substring("${workspace_loc}".length());

			fLog.debug("    base_loc: " + base_loc);

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

			fLog.debug("base_dir=" + base_dir);

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					File path_f_t = new File(base_dir_p.toFile(), path);
					try {
						if (path_f_t.exists()) {
							fLog.debug("Path does exist outside the project: "
									+ path_f_t.getCanonicalPath());
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
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(fCache,
				file_tree);

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

	protected IPreProcMacroProvider createPreProcMacroProvider(SVDBFileTree file) {
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(
				fCache);
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
				fLog.debug("Searching for \"" + leaf + "\" in global (ret="
						+ ret + ")");
			} else {
				fLog.debug("IncludeFileProvider not set");
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
				invalidateIndex();
				file_tree = findFileTree(path);
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

		fLog.debug("Processed pre-proc file");

//		fFileSystemProvider.clearMarkers(file_tree.getFilePath());
		file_tree.setSVDBFile(svdb_pp);
		// addIncludeFiles(file_tree, file_tree.getSVDBFile());

		dp.setMacroProvider(createMacroProvider(file_tree));
		SVDBFile svdb_f = factory.parse(copier.copy(), file_tree.getFilePath(),
				markers);
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));

		// propagateMarkersPreProc2DB(file_tree, svdb_pp, svdb_f);
		// addMarkers(path, svdb_f);

		return svdb_f;
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public synchronized SVDBFile findFile(String path) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);

		SVDBFile ret;

		ret = fCache.getFile(new NullProgressMonitor(), path);

		if (ret == null) {
			SVDBFileTree ft_root = fCache.getFileTree(new NullProgressMonitor(), path);
			
			if (ft_root == null) {
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.error("File Path \"" + path + "\" not in index", e);
					for (String p : getFileList(new NullProgressMonitor())) {
						System.out.println("path: " + p);
					}
				}
					
			}
			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			processFile(ft_root, mp);
			ret = fCache.getFile(new NullProgressMonitor(), path);
			
			/*
			if (ret != null) {
				fCache.setFile(path, ret);
			}
			 */
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

		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path
				.getFilePath()));

		fFileSystemProvider.clearMarkers(path_s);

		// Reflect markers from pre-processor to index database
		// propagateMarkersPreProc2DB(path, fPreProcFileMap.get(path_s),
		// svdb_f);
		// addMarkers(path_s, svdb_f);

		/*
		 * if (fIndexFileMap.containsKey(path.getFilePath())) { // Merge the
		 * files together. This happens during an update SVDBFile existing =
		 * fIndexFileMap.get(path.getFilePath()); SVDBFileMerger.merge(existing,
		 * svdb_f, null, null, null);
		 * existing.setLastModified(svdb_f.getLastModified()); } else { // Just
		 * add the file. This happens on first parse
		 * fIndexFileMap.put(path.getFilePath(), svdb_f); }
		 */
		fCache.setFile(path.getFilePath(), svdb_f);
		fCache.setMarkers(path.getFilePath(), markers);

		/*
		 * // Now, recurse through the files included for (SVDBFileTree ft_t :
		 * path.getIncludedFiles()) { // Note: process files that are currently
		 * not in the FileIndex, // but are in the pre-processor list. This
		 * ensures that we // don't try to process files included from another
		 * index if (!fIndexFileMap.containsKey(ft_t.getFilePath()) &&
		 * fPreProcFileMap.containsKey(ft_t.getFilePath())) { mp =
		 * createMacroProvider(ft_t); processFile(ft_t, mp); } }
		 */

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

		try {
			in.close();
		} catch (IOException e) {
		}

		SVDBFile file = ob.getFiles().get(0);

		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));

		return file;
	}

	public synchronized SVDBFileTree findFileTree(String path) {
		ensureIndexState(new NullProgressMonitor(), IndexState_FileTreeValid);
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path);
		if (ft == null) {
			// TODO:
			/*
			 * // First, see if the file actually exists if
			 * (getFileSystemProvider().fileExists(path)) { // invalidate the
			 * index rebuildIndex();
			 * 
			 * // Ensure database is built getFileDB(monitor);
			 * getFileTreeMap(monitor);
			 * 
			 * file_tree = fFileTreeMap.get(path); } else {
			 * fLog.error("parse: File \"" + path + "\" not in FileTreeMap of "
			 * + getResolvedBaseLocation() + " and does not exist"); return
			 * null; }
			 * 
			 * if (file_tree == null) { fLog.error("parse: File \"" + path +
			 * "\" not in FileTreeMap of " + getResolvedBaseLocation()); for
			 * (SVDBFileTree ft : fFileTreeMap.values()) { fLog.error("    " +
			 * ft.getFilePath()); } return null; }
			 */
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

	public SVPreProcScanner createPreProcScanner(String path) {
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
		// pp.setScanner(this);
		// pp.setObserver(this);

		pp.init(in, path);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(true);

		return pp;
	}

}
