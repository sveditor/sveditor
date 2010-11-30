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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

public class SVDBArgFileIndex extends SVDBLibIndex {
	private String						fBaseLocationDir;
	private long						fArgFileLastModified;
	protected List<String>				fFilePaths;
	protected Map<String, String>		fDefineMap;
	
	public SVDBArgFileIndex(
			String						project,
			String						root,
			ISVDBFileSystemProvider		fs_provider) {
		super(project, root, fs_provider);
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex");
		
		fFilePaths 			= new ArrayList<String>();
		fIncludePaths 		= new ArrayList<String>();
		fDefineMap			= new HashMap<String, String>();
	}
	
	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
	@Override
	public String getTypeName() {
		return "ArgFileIndex";
	}

	private String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			fBaseLocationDir = SVFileUtils.getPathParent(getResolvedBaseLocation());
		}
		return fBaseLocationDir;
	}

	@Override
	public void dump(IDBWriter index_data) {
		// Save the last-modified time for the arg file
		long last_modified = fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation());
		index_data.writeLong(last_modified);
		
		super.dump(index_data);
	}

	@Override
	public void load(
			IDBReader 		index_data, 
			List<SVDBFile> 	pp_files,
			List<SVDBFile> 	db_files) throws DBFormatException {
		fArgFileLastModified = index_data.readLong();
		fLoadUpToDate = true;
		
		fLog.debug("load - pp_files.size=" + pp_files.size() + " db_files.size=" + db_files.size());
		
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

		// Load up file paths from the .f target 
		initPaths();

		load_base(index_data, pp_files, db_files);
		
		if (isLoaded()) {
			fLog.debug("Index is loaded... Loading markers and FileTreeMap");

			// re-build the FileTree structure
			for (String file : fFilePaths) {
				file = resolvePath(file);
				SVDBFile pp_file = findPreProcFile(file);
				
				fLog.debug("    Building FileTree for \"" + file + "\"");
				
				if (pp_file == null) {
					fLog.error("Failed to find pre-proc file \"" + file + "\"");
					continue;
				}
				
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}
			
			loadMarkers();
		} else {
			fLog.debug("Index is not loaded...");
		}
	}

	@Override
	protected boolean isLoadUpToDate() {
		fLog.debug("BaseLocation Exists: " + 
				fFileSystemProvider.fileExists(getResolvedBaseLocation()) + 
				" ArgFileLastModified (saved): " + fArgFileLastModified + 
				" ArgFileLastModified (current): " + fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation()));
		if (fFileSystemProvider.fileExists(getResolvedBaseLocation()) &&
				fArgFileLastModified >= fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation())) {
			return super.isLoadUpToDate();
		}
		return false;
	}
	
	@Override
	public void fileChanged(String path) {
		if (path.equals(getResolvedBaseLocation())) {
			rebuildIndex();
		} else {
			super.fileChanged(path);
		}
	}

	@Override
	protected void buildPreProcFileMap() {
		initPaths();
		
		// Say the index is already valid
		fPreProcFileMapValid = true;
		
		for (String file : fFilePaths) {
			String r_file = resolvePath(file);
			fLog.debug("Resolved path for \"" + file + "\" is \"" + r_file + "\"");
			SVDBFile pp_file = processPreProcFile(r_file, true);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + r_file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}
	
	@Override
	protected IPreProcMacroProvider createMacroProvider(SVDBFileTree fileTree) {
		
		IPreProcMacroProvider mp = super.createMacroProvider(fileTree); 
		for (Entry<String, String> entry : fDefineMap.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
			
		return mp; 
	}
	
	public IPreProcMacroProvider pub_createMacroProvider(SVDBFileTree ft) {
		return createMacroProvider(ft);
	}
	
	@Override
	protected IPreProcMacroProvider createPreProcMacroProvider(SVDBFileTree file) {
		IPreProcMacroProvider mp = super.createPreProcMacroProvider(file);
		
		for (Entry<String, String> entry : fDefineMap.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		
		return mp;
	}

	@Override
	protected void initPaths() {
		fFilePaths.clear();
		fIncludePaths.clear();
		fDefineMap.clear();
		fDefineMap.putAll(fGlobalDefines);
		
		// Add an include path for the arg file location
		fIncludePaths.add(SVFileUtils.getPathParent(getResolvedBaseLocation()));
		
		InputStream in = fFileSystemProvider.openStream(getResolvedBaseLocation());
		
		if (in != null) {
			ITextScanner sc = new InputStreamTextScanner(in, getResolvedBaseLocation());
			SVFScanner scanner = new SVFScanner();
			
			try {
				scanner.scan(sc);
			} catch (Exception e) {
				fLog.error("Failed to read argument file \"" + 
						getResolvedBaseLocation() + "\"", e);
			}
			
			for (String f : scanner.getFilePaths()) {
				String exp_f = SVDBIndexUtil.expandVars(f, true);
				fLog.debug("[FILE PATH] " + f + " (" + exp_f + ")");
				fFilePaths.add(exp_f);
			}
			
			for (String inc : scanner.getIncludePaths()) {
				fLog.debug("[INC PATH] " + inc + " (" + SVDBIndexUtil.expandVars(inc, true) + ")");
				fIncludePaths.add(SVDBIndexUtil.expandVars(inc, true));
			}
			
			for (Entry<String, String> entry : scanner.getDefineMap().entrySet()) {
				fLog.debug("[DEFINE] " + entry.getKey() + "=" + entry.getValue());
				fDefineMap.put(entry.getKey(), entry.getValue());
			}
			
			fFileSystemProvider.closeStream(in);
		} else {
			fLog.error("failed to open file \"" + getResolvedBaseLocation() + "\"");
		}
	}
	
	@Override
	protected void buildIndex() {
		getPreProcFileMap(); // force pre-proc info to be built

		for (String file : fFilePaths) {
			file = resolvePath(file);
			SVDBFile pp_file = findPreProcFile(file);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = fFileTreeMap.get(file);
			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			
			processFile(ft_root, mp);
		}
		
		fIndexFileMapValid = true;
		
		signalIndexRebuilt();
	}
	
	@Override
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		SVDBSearchResult<SVDBFile> ret = null;
		
		if ((ret = super.findIncludedFile(path)) != null) {
			return ret;
		}
		
		// Otherwise, search through each include path
		for (String inc : fIncludePaths) {
			inc = resolvePath(inc);
			inc = inc + "/" + path;
			
			if (fFileSystemProvider.fileExists(inc)) {
				SVDBFile pp_file = processPreProcFile(inc, true);
				
				ret = new SVDBSearchResult<SVDBFile>(pp_file, this);
				break;
			}
		}
		
		return ret;
	}

	protected String resolvePath(String path_orig) {
		String path = path_orig;
		String norm_path = null;

		// relative to the base location
		if (path.startsWith("..")) {
			path = getResolvedBaseLocationDir() + "/" + path;
			norm_path = normalizePath(path);
			
			if (getBaseLocation().startsWith("${workspace_loc}") && 
					!fFileSystemProvider.fileExists(norm_path)) {
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
					base_dir = root.getProject(base_loc.substring(1));
				}
				
				if (base_dir != null && base_dir.exists()) {
					IPath base_dir_p = base_dir.getLocation();
					if (base_dir_p != null) {
						File path_f_t = new File(base_dir_p.toFile(), path_orig);
						try {
							if (path_f_t.exists()) {
								fLog.debug("Path does exist outside the project: " + path_f_t.getCanonicalPath());
								norm_path = SVFileUtils.normalize(path_f_t.getCanonicalPath());
							}
						} catch (IOException e) {
							e.printStackTrace();
						}
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
		
		return norm_path;
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

		/*
		if (skipCnt > 0) {
			// throw new RuntimeException("exceeded skipCnt while normalizing \"" + path + "\"");
		} 
		 */
		return ret.reverse().toString();
	}

}
