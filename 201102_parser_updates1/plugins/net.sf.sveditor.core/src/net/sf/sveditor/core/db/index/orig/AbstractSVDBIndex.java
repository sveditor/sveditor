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


package net.sf.sveditor.core.db.index.orig;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Pattern;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexRegistry;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;


public abstract class AbstractSVDBIndex implements ISVDBIndex {
	protected String							fProjectName;
	protected Map<String, SVDBFile>				fIndexFileMap;
	protected boolean							fIndexFileMapValid;

	protected Map<String, SVDBFile>				fPreProcFileMap;
	protected boolean							fPreProcFileMapValid;

	protected ISVDBIncludeFileProvider			fIncludeFileProvider;
	
	protected List<ISVDBIndexChangeListener>	fIndexChageListeners;

	protected ISVDBIndexRegistry				fIndexRegistry;
	
	protected static Pattern					fWinPathPattern;
	protected static final List<String>			fSVExtensions;
	protected static final List<String>			fIgnoreDirs;
	protected LogHandle							fLog;
	protected ISVDBFileSystemProvider			fFileSystemProvider;
	protected Map<String, String>				fGlobalDefines;
	protected boolean							fLoadUpToDate;
	protected ISVDBIndexCache					fCache;
	
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
		
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fIndexFileMap = new HashMap<String, SVDBFile>();
		fGlobalDefines = new HashMap<String, String>();
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
		
	}

	public AbstractSVDBIndex(
			String 						project, 
			ISVDBFileSystemProvider 	fs_provider,
			ISVDBIndexCache				cache) {
		this(project);
		setFileSystemProvider(fs_provider);
		fCache = cache;
	}
	
	public List<String> getFileList(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
	}
	
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}
	
	public void setGlobalDefine(String key, String val) {
		fLog.debug("setGlobalDefine(" + key + ", " + val + ")");
		
		// Rebuild the index when something changes
		if (!fGlobalDefines.containsKey(key) ||
				!fGlobalDefines.get(key).equals(val)) {
			rebuildIndex();
		}
		
		if (fGlobalDefines.containsKey(key)) {
			fGlobalDefines.remove(key);
		}
		fGlobalDefines.put(key, val);
	}
	
	public void clearGlobalDefines() {
		fGlobalDefines.clear();
	}

	public void init(ISVDBIndexRegistry registry) {
		fIndexRegistry = registry;
	}
	

	public void init(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		
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
		return (fIndexFileMapValid && fPreProcFileMapValid);
	}
	
	protected IPreProcMacroProvider createMacroProvider(SVDBFileTree file_tree) {
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(null, file_tree);
		
		for (Entry<String, String> entry : fGlobalDefines.entrySet()) {
			mp.setMacro(entry.getKey(), entry.getValue());
		}
		
		return mp;
	}
	
	protected IPreProcMacroProvider createPreProcMacroProvider(SVDBFileTree file) {
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null);
		mp.setFileContext(file);

		for (Entry<String, String> entry : fGlobalDefines.entrySet()) {
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
	}

	public void load(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
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
	}

	protected void load_base(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException {
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
	}			

	protected abstract boolean isLoadUpToDate();

	public synchronized Map<String, SVDBFile> getFileDB(IProgressMonitor monitor) {
		if (!fIndexFileMapValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fIndexFileMapValid) {
			buildIndex(monitor);
		}
		
		return fIndexFileMap;
	}

	protected abstract void buildIndex(IProgressMonitor monitor);

	public synchronized Map<String, SVDBFile> getPreProcFileMap(IProgressMonitor monitor) {
		if (!fPreProcFileMapValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fPreProcFileMapValid) {
			buildPreProcFileMap();
		}
		
		return fPreProcFileMap;
	}

	protected abstract void buildPreProcFileMap();

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		/** TEMP
		return new SVDBIndexItemIterator(getFileDB(monitor));
		 */
		return null;
	}
	
	public SVDBFile findFile(String path) {
		Map<String, SVDBFile> map = getFileDB(new NullProgressMonitor());
		
		return map.get(path);
	}

	public SVDBFile findPreProcFile(String path) {
		Map<String, SVDBFile> map = getPreProcFileMap(new NullProgressMonitor());
		return map.get(path);
	}
	

	public void dispose() {
		if (fFileSystemProvider != null) {
			fFileSystemProvider.dispose();
		}
	}
}

