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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Pattern;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

public abstract class AbstractSVDBIndex implements ISVDBIndex {
	protected String						fProjectName;
	protected Map<String, SVDBFile>			fFileIndex;
	protected boolean						fFileIndexValid;

	protected Map<String, SVDBFile>			fFileList;
	protected boolean						fFileListValid;

	protected ISVDBIncludeFileProvider		fIncludeFileProvider;

	protected ISVDBIndexRegistry			fIndexRegistry;
	
	protected static Pattern				fWinPathPattern;
	protected static final List<String>		fSVExtensions;
	protected static final List<String>		fIgnoreDirs;
	protected LogHandle						fLog;
	protected ISVDBFileSystemProvider		fFileSystemProvider;
	protected Map<String, String>			fGlobalDefines;
	
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

	public AbstractSVDBIndex(String project) {
		fProjectName = project;
		
		fFileList = new HashMap<String, SVDBFile>();
		fFileIndex = new HashMap<String, SVDBFile>();
		fGlobalDefines = new HashMap<String, String>();
	}

	public AbstractSVDBIndex(String project, ISVDBFileSystemProvider fs_provider) {
		fProjectName 			= project;
		fFileSystemProvider 	= fs_provider;
		
		fFileList 				= new HashMap<String, SVDBFile>();
		fFileIndex 				= new HashMap<String, SVDBFile>();
		fGlobalDefines = new HashMap<String, String>();
	}
	
	public void setGlobalDefine(String key, String val) {
		if (fGlobalDefines.containsKey(key)) {
			fGlobalDefines.remove(key);
		}
		fGlobalDefines.put(key, val);
	}

	public void init(ISVDBIndexRegistry registry) {
		fIndexRegistry = registry;
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider provider) {
		fIncludeFileProvider = provider;
	}

	public boolean isLoaded() {
		return (fFileIndexValid && fFileListValid);
	}
	
	protected IPreProcMacroProvider createMacroProvider(SVDBFileTree file_tree) {
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(file_tree);
		
		for (Entry<String, String> entry : fGlobalDefines.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		
		return mp;
	}
	
	protected IPreProcMacroProvider createPreProcMacroProvider(SVDBFileTree file) {
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider();
		mp.setFileContext(file);

		for (Entry<String, String> entry : fGlobalDefines.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}

		return mp;
	}
	
	/**
	 * Search for an include file locally
	public SVDBFile findIncludedFile(String leaf) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		
		Iterator<String> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			String f = it.next();
			
			String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
				return map.get(f);
			}
		}
		
		return null;
	}
	 */
	
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
		// Dump nothing...
	}

	public void load(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
		load_base(index_data, pp_files, db_files);
	}

	protected void load_base(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
		fFileList.clear();
		fFileIndex.clear();
		
		for (SVDBFile f : pp_files) {
			fFileList.put(f.getFilePath(), f);
		}
		
		for (SVDBFile f : db_files) {
			fFileIndex.put(f.getFilePath(), f);
		}

		if (isLoadUpToDate()) {
			fLog.debug("index \"" + getBaseLocation() + "\" IS up-to-date");
			fFileIndexValid = true;
			fFileListValid  = true;
		} else {
			fLog.debug("index \"" + getBaseLocation() + "\" NOT up-to-date");
			fFileIndexValid = false;
			fFileListValid  = false;
			fFileList.clear();
			fFileIndex.clear();
		}
	}			

	protected abstract boolean isLoadUpToDate();

	public synchronized Map<String, SVDBFile> getFileDB() {
		if (!fFileIndexValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fFileIndexValid) {
			buildIndex();
		}
		
		return fFileIndex;
	}

	protected abstract void buildIndex();

	public synchronized Map<String, SVDBFile> getPreProcFileMap() {
		if (!fFileListValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fFileListValid) {
			buildPreProcFileMap();
		}
		
		return fFileList;
	}

	protected abstract void buildPreProcFileMap();

	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		return new SVDBIndexItemIterator(getFileDB());
	}
	
	public SVDBFile findFile(String path) {
		Map<String, SVDBFile> map = getFileDB();
		
		return map.get(path);
	}

	public SVDBFile findPreProcFile(String path) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		return map.get(path);
	}
	

	public void dispose() {
		if (fFileSystemProvider != null) {
			fFileSystemProvider.dispose();
		}
	}
	
	protected static String expandVars(
			String 			path,
			boolean			expand_env_vars) {
		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}

		if (expand_env_vars) {
			StringBuilder sb = new StringBuilder(exp_path);
			StringBuilder tmp = new StringBuilder();
			int idx = 0;
			
			while (idx < sb.length()) {
				if (sb.charAt(idx) == '$') {
					tmp.setLength(0);
					
					int start = idx, end;
					String key, val=null;
					idx++;
					if (sb.charAt(idx) == '{') {
						idx++;
						
						while (idx < sb.length() && sb.charAt(idx) != '}') {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						if (idx < sb.length()) {
							end = ++idx;
						} else {
							end = idx;
						}
					} else {
						while (idx < sb.length() && 
								sb.charAt(idx) != '/' && !Character.isWhitespace(sb.charAt(idx))) {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = (idx-1);
					}

					key = tmp.toString();
					if ((val = System.getenv(key)) != null) {
						sb.replace(start, end, val);
					}
				} else {
					idx++;
				}
			}
			
			exp_path = sb.toString();
		}

		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		try {
			exp_path = mgr.performStringSubstitution(exp_path);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}
	
}
