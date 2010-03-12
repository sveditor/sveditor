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
		
		load_base(index_data, pp_files, db_files);
		
		if (isLoaded()) {

			// re-build the FileTree structure
			for (String file : fFilePaths) {
				file = resolvePath(file);
				SVDBFile pp_file = findPreProcFile(file);
				
				if (pp_file == null) {
					fLog.error("Failed to find file \"" + file + "\"");
					continue;
				}
				
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}
			
			loadMarkers();
		}
	}

	@Override
	protected boolean isLoadUpToDate() {
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
				fLog.debug("[FILE PATH] " + f);
				fFilePaths.add(SVDBIndexUtil.expandVars(f, true));
			}
			
			for (String inc : scanner.getIncludePaths()) {
				fLog.debug("[INC PATH] " + inc + " (" + SVDBIndexUtil.expandVars(inc, true) + ")");
				fIncludePaths.add(SVDBIndexUtil.expandVars(inc, true));
			}
			
			for (Entry<String, String> entry : scanner.getDefineMap().entrySet()) {
				fLog.debug("[DEFINE] " + entry.getKey() + "=" + entry.getValue());
				fDefineMap.put(entry.getKey(), entry.getValue());
			}
			
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
			}
		}
		
		return ret;
	}

	protected String resolvePath(String path) {
		
		// relative to the base location
		if (path.startsWith("..")) {
			path = getResolvedBaseLocationDir() + "/" + path;
		} else if (path.startsWith(".") || Character.isJavaIdentifierStart(path.charAt(0))) {
			if (path.equals(".")) {
				path = getResolvedBaseLocationDir();
			} else if (path.startsWith(".")) { 
				path = getResolvedBaseLocationDir() + "/" + path.substring(2);
			} else {
				// This path is an implicit relative path that is 
				// relative to the base directory
				path = getResolvedBaseLocationDir() + "/" + path;
			}
		}
		
		String norm_path = normalizePath(path);
		
		return norm_path;
	}
	
	protected String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();
		
		int i=path.length()-1;
		int end;
		int skipCnt = 0;
		
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
		
		if (skipCnt > 0) {
			throw new RuntimeException("exceeded skipCnt");
		}
		
		return ret.reverse().toString();
	}

}
