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
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
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


public abstract class AbstractSVDBIndex implements ISVDBIndex {
	private String							fProjectName;
	private String							fBaseLocation;
	private String							fResolvedBaseLocation;
	private String							fBaseLocationDir;
	
	private SVDBBaseIndexCacheData			fIndexCacheData;
	

	private ISVDBIncludeFileProvider		fIncludeFileProvider;
	
	private List<ISVDBIndexChangeListener>	fIndexChageListeners;

	protected static Pattern				fWinPathPattern;
	protected static final List<String>		fSVExtensions;
	protected static final List<String>		fIgnoreDirs;
	protected LogHandle						fLog;
	protected ISVDBFileSystemProvider		fFileSystemProvider;

	protected boolean						fLoadUpToDate;
	private ISVDBIndexCache					fCache;
	
	/**
	 * True if the root file list is valid. 
	 */
	protected boolean							fRootFileListValid;
	
	protected boolean							fPreProcessorMapValid;
	
	protected boolean							fFileTreeMapValid;
	
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
		
		fProjectName = project;
		
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
	}

	public AbstractSVDBIndex(
			String 						project,
			String						base_location,
			ISVDBFileSystemProvider 	fs_provider,
			ISVDBIndexCache				cache) {
		this(project);
		fBaseLocation = base_location;
		setFileSystemProvider(fs_provider);
		fCache = cache;
	}

	/**
	 * Initialize the index 
	 * @param monitor
	 */
	public void init(IProgressMonitor monitor) {
		SubProgressMonitor m;
		monitor.beginTask("Initialize index " + getBaseLocation(), 100);
		
		// Initialize the cache
		m = new SubProgressMonitor(monitor, 1);
		fIndexCacheData = createIndexCacheData();
		fCache.init(m, fIndexCacheData);
		
		// If 
		boolean valid = true;
		if (fCache.getFileList().size() > 0) {
			
			for (String path : fCache.getFileList()){
				long fs_timestamp = fFileSystemProvider.getLastModifiedTime(path);
				long cache_timestamp = fCache.getLastModified(path);
				if (fs_timestamp != cache_timestamp) {
					System.out.println("path: " + path + " fs_timestamp=" + fs_timestamp + " cache_timestamp=" + cache_timestamp);
					valid = false;
					break;
				}
			}
		} else {
			valid = false;
		}
		
		if (valid) {
			System.out.println("Cache is valid");
			fRootFileListValid = true;
			fPreProcessorMapValid = true;
			fFileTreeMapValid = true;
		} else {
			System.out.println("Cache is invalid");
			fRootFileListValid = false;
			fPreProcessorMapValid = false;
			fFileTreeMapValid = false;
			fCache.clear();
		}

		monitor.done();
	}

	public void rebuildIndex() {
		// TODO Auto-generated method stub
	}

	protected ISVDBIndexCache getCache() {
		return fCache;
	}
	
	protected SVDBBaseIndexCacheData getCacheData() {
		return fIndexCacheData;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
	}
	
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public String getResolvedBaseLocation() {
		if (fResolvedBaseLocation == null) {
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(fBaseLocation, true);
		}
		
		return fResolvedBaseLocation;
	}
	
	public String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			String base_location = getResolvedBaseLocation();
			if (fFileSystemProvider.isDir(base_location)) {
				fBaseLocationDir = base_location;
			} else {
				fBaseLocationDir = SVFileUtils.getPathParent(base_location);
			}
		}
		return fBaseLocationDir;
	}
	
	public void setGlobalDefine(String key, String val) {
		fLog.debug("setGlobalDefine(" + key + ", " + val + ")");
		fIndexCacheData.setGlobalDefine(key, val);
		
		// Rebuild the index when something changes
		if (!fIndexCacheData.getGlobalDefines().containsKey(key) ||
				!fIndexCacheData.getGlobalDefines().get(key).equals(val)) {
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
	 * getFileList() -- returns a list of files handled by this index
	 * The file list is valid after:
	 * - Root File discovery
	 * - Pre-processor parse 
	 */
	public List<String> getFileList(IProgressMonitor monitor) {
		if (!fRootFileListValid) {
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			discoverRootFiles(m);
			fRootFileListValid = true;
			fPreProcessorMapValid = false;
		}
		
		if (!fPreProcessorMapValid) {
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			preProcessFiles(m);
		}
		
		if (!fFileTreeMapValid) {
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			buildFileTree(m);
		}
		
		return fCache.getFileList();
	}
	
	protected void addFile(String path) {
		fCache.addFile(path);
	}
	
	protected void clearFilesList() {
		fCache.clear();
	}
	
	/**
	 * Creates 
	 * @return
	 */
	protected SVDBBaseIndexCacheData createIndexCacheData() {
		return new SVDBBaseIndexCacheData();
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
		
		for (int i=0; i<paths.size(); i++) {
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
		monitor.beginTask("Building File Tree", paths.size());
		
		for (int i=0; i<paths.size(); i++) {
			String path = paths.get(i);
			if (fCache.getFileTree(new NullProgressMonitor(), path) == null) {
				SVDBFile pp_file = fCache.getPreProcFile(new NullProgressMonitor(), path);
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}
		}
		
		monitor.done();
	}
	
	private void buildPreProcFileMap(
			SVDBFileTree parent, 
			SVDBFileTree root) {
		SVDBFileTreeUtils	ft_utils = new SVDBFileTreeUtils();
		SVDBFile			file = root.getSVDBFile();

		if (parent != null) {
			root.getIncludedByFiles().add(parent.getFilePath());
		}
		
		ft_utils.resolveConditionals(root, 
				new SVPreProcDefineProvider(createPreProcMacroProvider(root)));
		
		fCache.setFileTree(root.getFilePath(), root);
		
		addPreProcFileIncludeFiles(root, root.getSVDBFile());
	}
	
	private void addPreProcFileIncludeFiles(
			SVDBFileTree			root,
			ISVDBScopeItem			scope) {
		for (int i=0; i<scope.getItems().size(); i++) {
			ISVDBItemBase it = scope.getItems().get(i);

			if (it.getType() == SVDBItemType.Include) {
				fLog.debug("Include file: " + ((ISVDBNamedItem)it).getName());
				
				// Look local first
				SVDBSearchResult<SVDBFile> f = findIncludedFileGlobal(((ISVDBNamedItem)it).getName());
				
				if (f != null) {
					fLog.debug("Found include file \"" + ((ISVDBNamedItem)it).getName() + "\" in index \"" + 
							f.getIndex().getBaseLocation() + "\"");
					fLog.debug("Adding included file \"" + ((ISVDBNamedItem)it).getName() + " to FileTree \"" +
							root.getFilePath() + "\"");
					SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.getItem().duplicate());
					root.getIncludedFiles().add(ft.getFilePath());
					buildPreProcFileMap(root, ft);
				} else {
					fLog.debug("Failed to find include file \"" + ((ISVDBNamedItem)it).getName() + 
							"\" (from file " + root.getFilePath() + ")");
					SVDBFileTree ft = new SVDBFileTree(SVDBItem.getName(it));
					root.getIncludedFiles().add(ft.getFilePath());
					ft.getIncludedByFiles().add(root.getFilePath());
					
					// Create a marker for the missing include file
					SVDBFile real_svdb = fCache.getPreProcFile(new NullProgressMonitor(), root.getFilePath());
					if (real_svdb != null) {
						SVDBMarker err = new SVDBMarker(SVDBMarker.MARKER_ERR,
								SVDBMarker.KIND_MISSING_INC,
								"Failed to find include file \"" + ((ISVDBNamedItem)it).getName() + "\"");
						err.setAttr(SVDBMarker.MISSING_INC_PATH, ((ISVDBNamedItem)it).getName());
						real_svdb.addItem(err);
						err.setLocation(it.getLocation());
					} else {
						fLog.error("Failed to find PreProc file for \"" + root.getFilePath() + "\"");
					}
				}
			} else if (it instanceof ISVDBScopeItem) {
				addPreProcFileIncludeFiles(root, (ISVDBScopeItem)it);
			}
		}
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		
		for (String inc_dir : fIndexCacheData.getIncludePaths()) {
			String inc_path = resolvePath(inc_dir + "/" + path);
			SVDBFile file = null;

			fLog.debug("Include Path: \"" + inc_path + "\"");

			if ((file = fCache.getPreProcFile(new NullProgressMonitor(), inc_path)) != null) {
				fLog.debug("findIncludedFile: \"" + inc_path + "\" already in map");
			} else {
				if (fFileSystemProvider.fileExists(inc_path)) {
					fLog.debug("findIncludedFile: building entry for \"" + inc_path + "\"");

					file = processPreProcFile(inc_path);
					fCache.addFile(inc_path);
					fCache.setPreProcFile(inc_path, file);
					fCache.setLastModified(inc_path, file.getLastModified());
				} else {
					fLog.debug("findIncludedFile: file \"" + inc_path + "\" does not exist");
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
			if ((norm_path = resolveRelativePath(getResolvedBaseLocationDir(), path)) == null) {
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break; 
					}
				}
			}
		} else {
			if (path.equals(".")) {
				path = getResolvedBaseLocationDir();
			} else if (path.startsWith(".")) { 
				path = getResolvedBaseLocationDir() + "/" + path.substring(2);
			} else {
				if (!fFileSystemProvider.fileExists(path)) {
					//  See if this is an implicit path
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
		
		return (norm_path != null)?norm_path:path_orig;
	}
	
	private String resolveRelativePath(String base, String path) {
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base + "/" + path);

		if (fFileSystemProvider.fileExists(norm_path)) {
			return norm_path;
		} else if (getBaseLocation().startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path 
			// by computing the absolute path
			String base_loc = getResolvedBaseLocationDir();
			base_loc = base_loc.substring("${workspace_loc}".length());

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer base_dir = null;
			try {
				base_dir = root.getFolder(new Path(base_loc));
			} catch (IllegalArgumentException e) {}

			if (base_dir == null) {
				if (base_loc.length() > 0) {
					base_dir = root.getProject(base_loc.substring(1));
				}
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					File path_f_t = new File(base_dir_p.toFile(), path);
					try {
						if (path_f_t.exists()) {
							fLog.debug("Path does exist outside the project: " + path_f_t.getCanonicalPath());
							norm_path = SVFileUtils.normalize(path_f_t.getCanonicalPath());
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
		
		int i=path.length()-1;
		int end;
		int skipCnt = 0;
		
		// First, skip any trailing '/'
		while (i >=0 && (path.charAt(i) == '/' || path.charAt(i) == '\\')) {
			i--;
		}
		
		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();
			
			while (i>=0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}
			
			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length()-1);
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
	
	public boolean isLoaded() {
		/**
		return (fIndexFileMapValid && fPreProcFileMapValid);
		 */
		return false; // deprecated
	}
	
	protected IPreProcMacroProvider createMacroProvider(SVDBFileTree file_tree) {
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(fCache, file_tree);
		
		for (Entry<String, String> entry : fIndexCacheData.getDefines().entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		
		return mp;
	}
	
	protected IPreProcMacroProvider createPreProcMacroProvider(SVDBFileTree file) {
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(fCache);
		mp.setFileContext(file);

		for (Entry<String, String> entry : fIndexCacheData.getDefines().entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		
		return mp;
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFileGlobal(String leaf) {
		SVDBSearchResult<SVDBFile> ret = findIncludedFile(leaf);
		
		if (ret == null) {
			if (fIncludeFileProvider != null) {
				ret = fIncludeFileProvider.findIncludedFile(leaf);
				fLog.debug("Searching for \"" + leaf + "\" in global (ret=" + ret + ")");
			} else {
				fLog.debug("IncludeFileProvider not set");
			}
		}
		
		return ret;
	}
	
	public void dump(IDBWriter index_data) {
		/*
		try {
			// Dump Global Defines, so we can check for changes on restart
			index_data.writeInt(fGlobalDefines.size());
			for (Entry<String, String> def : fGlobalDefines.entrySet()) {
				index_data.writeString(def.getKey());
				index_data.writeString(def.getValue());
			}
		} catch (DBWriteException e) {
			fLog.error("Problem writing ", e);
		}
		 */
	}

	public void load(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
/*		
		fLoadUpToDate = true;
		
		// Read back the Global Defines. Project settings will already
		// be set.  
		int n_defines = index_data.readInt();
		for (int i=0; i<n_defines; i++) {
			String key = index_data.readString();
			String val = index_data.readString();
			
			if (fGlobalDefines.containsKey(key) ||
					!fGlobalDefines.get(key).equals(val)) {
				fGlobalDefines.remove(key);
				fGlobalDefines.put(key, val);
				fLog.debug("Invalidating load, since key " + key + " changed value");
				fLoadUpToDate = false;
			}
		}
		
		load_base(index_data, pp_files, db_files);
 */
	}

	protected void load_base(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
/*		
		fPreProcFileMap.clear();
		fIndexFileMap.clear();
		
		for (SVDBFile f : pp_files) {
			fPreProcFileMap.put(f.getFilePath(), f);
		}
		
		for (SVDBFile f : db_files) {
			fIndexFileMap.put(f.getFilePath(), f);
		}

		if (fLoadUpToDate && isLoadUpToDate()) {
			fLog.debug("index \"" + getBaseLocation() + "\" IS up-to-date");
			fIndexFileMapValid = true;
			fPreProcFileMapValid  = true;
		} else {
			fLog.debug("index \"" + getBaseLocation() + "\" NOT up-to-date");
			rebuildIndex();
		}
 */		
	}
	
	public SVDBFile parse(InputStream in, String path, IProgressMonitor monitor) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(null);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);

		path = SVFileUtils.normalize(path);

		InputStreamCopier copier = new InputStreamCopier(in);
		in = null;

		// Ensure database is built
		// getFileDB(monitor);

		SVDBFileTree file_tree = findFileTree(path);

		if (file_tree == null) {
			// TODO: is this really correct?
			return null;
		}

		SVPreProcScanner 	sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();
		sc.setObserver(ob);

		file_tree = file_tree.duplicate();

		sc.init(copier.copy(), path);
		sc.scan();

		SVDBFile svdb_pp = ob.getFiles().get(0);

		fLog.debug("Processed pre-proc file");

		fFileSystemProvider.clearMarkers(file_tree.getFilePath());
		file_tree.setSVDBFile(svdb_pp);
//		addIncludeFiles(file_tree, file_tree.getSVDBFile());
		
		dp.setMacroProvider(createMacroProvider(file_tree));
		SVDBFile svdb_f = factory.parse(copier.copy(), file_tree.getFilePath());
		svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));

//		propagateMarkersPreProc2DB(file_tree, svdb_pp, svdb_f);
//		addMarkers(path, svdb_f);

		return svdb_f;
	}

	@Deprecated
	protected boolean isLoadUpToDate() {
		return true;
	}

	public synchronized Map<String, SVDBFile> getFileDB(IProgressMonitor monitor) {
/*		
		if (!fIndexFileMapValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fIndexFileMapValid) {
			buildIndex(monitor);
		}
		
		return fIndexFileMap; 
 */
		return null; // deprecated
	}

	public synchronized Map<String, SVDBFile> getPreProcFileMap(IProgressMonitor monitor) {
/*		
		if (!fPreProcFileMapValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fPreProcFileMapValid) {
			buildPreProcFileMap();
		}
		
		return fPreProcFileMap;
 */
		return null; // deprecated
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		
		return new SVDBIndexItemIterator(getFileList(new NullProgressMonitor()), this);
	}
	
	public SVDBFile findFile(String path) {
		// TODO: Ensure first steps are complete
		SVDBFile ret;
		
		ret = fCache.getFile(new NullProgressMonitor(), path);
		
		if (ret == null) {
			SVDBFileTree ft_root = fCache.getFileTree(new NullProgressMonitor(), path);
			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			processFile(ft_root, mp);
			ret = fCache.getFile(new NullProgressMonitor(), path);
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
	
	protected void processFile(
			SVDBFileTree				path,
			IPreProcMacroProvider 		mp) {
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp); 
		
		String path_s = path.getFilePath();

		InputStream in = fFileSystemProvider.openStream(path_s);
		
		if (in == null) {
			fLog.error("Failed to open file \"" + path_s + "\"");
		}
		
		BufferedInputStream in_b = new BufferedInputStream(in);

		SVDBFile svdb_f = factory.parse(in_b, path.getFilePath());

		// Problem parsing the file..
		if (svdb_f == null) {
			return;
		}
		
		svdb_f.setLastModified(
				fFileSystemProvider.getLastModifiedTime(path.getFilePath()));
		
		fFileSystemProvider.clearMarkers(path_s);
		
		// Reflect markers from pre-processor to index database
//		propagateMarkersPreProc2DB(path, fPreProcFileMap.get(path_s), svdb_f);
//		addMarkers(path_s, svdb_f);
	
		/*
		if (fIndexFileMap.containsKey(path.getFilePath())) {
			// Merge the files together. This happens during an update
			SVDBFile existing = fIndexFileMap.get(path.getFilePath());
			SVDBFileMerger.merge(existing, svdb_f, null, null, null);
			existing.setLastModified(svdb_f.getLastModified());
		} else {
			// Just add the file. This happens on first parse
			fIndexFileMap.put(path.getFilePath(), svdb_f);
		}
		 */
		fCache.setFile(path.getFilePath(), svdb_f);

		/*
		// Now, recurse through the files included
		for (SVDBFileTree ft_t : path.getIncludedFiles()) {
			// Note: process files that are currently not in the FileIndex, 
			// but are in the pre-processor list. This ensures that we 
			// don't try to process files included from another index
			if (!fIndexFileMap.containsKey(ft_t.getFilePath()) &&
					fPreProcFileMap.containsKey(ft_t.getFilePath())) {
				mp = createMacroProvider(ft_t);
				processFile(ft_t, mp);
			}
		}
		 */

		fFileSystemProvider.closeStream(in);
	}
	

	public SVDBFile findPreProcFile(String path) {
		return fCache.getPreProcFile(new NullProgressMonitor(), path);
	}
	
	protected SVDBFile processPreProcFile(String path) {
		SVPreProcScanner 	sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.setObserver(ob);
		
		fLog.debug("processPreProcFile: path=" + path);
		InputStream in = fFileSystemProvider.openStream(path);
		
		if (in == null) {
			fLog.error(getClass().getName() + ": failed to open \"" + path + "\"");
			return null;
		}

		sc.init(in, path);
		sc.scan();
		
		try {
			in.close();
		} catch (IOException e) { }

		SVDBFile file = ob.getFiles().get(0);
		
		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		
		return file;
	}
	
	
	public SVDBFileTree findFileTree(String path) {
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path);
		if (ft == null) {
			// TODO:
			/*
			// First, see if the file actually exists
			if (getFileSystemProvider().fileExists(path)) {
				// invalidate the index
				rebuildIndex();
				
				// Ensure database is built
				getFileDB(monitor);
				getFileTreeMap(monitor);
				
				file_tree = fFileTreeMap.get(path);
			} else {
				fLog.error("parse: File \"" + path + "\" not in FileTreeMap of " + getResolvedBaseLocation() + " and does not exist");
				return null;
			}
			
			if (file_tree == null) {
				fLog.error("parse: File \"" + path + "\" not in FileTreeMap of " + getResolvedBaseLocation());
				for (SVDBFileTree ft : fFileTreeMap.values()) {
					fLog.error("    " + ft.getFilePath());
				}
				return null;
			}
			 */
		}
		
		return ft;
	}
	

	public void dispose() {
		if (fFileSystemProvider != null) {
			fFileSystemProvider.dispose();
		}
		if (fCache != null) {
			fCache.sync();
		}
	}
	
	public SVPreProcScanner createPreProcScanner(String path) {
		InputStream in = getFileSystemProvider().openStream(path);
		SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), path);
		
		if (ft == null) {
//			Map<String, SVDBFileTree> m = getFileTreeMap(new NullProgressMonitor());
			fLog.error("Failed to find pre-proc file for \"" + path + "\"");
/*			
			fLog.debug("map.size=" + m.size());
			for (String p : m.keySet()) {
				fLog.debug("    " + p);
			}
 */			
			return null;
		}

		IPreProcMacroProvider mp = createMacroProvider(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);

		SVPreProcScanner pp = new SVPreProcScanner();
		pp.setDefineProvider(dp);
		//pp.setScanner(this);
		//pp.setObserver(this);

		pp.init(in, path);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(true);
		
		return pp;
	}
	
}

