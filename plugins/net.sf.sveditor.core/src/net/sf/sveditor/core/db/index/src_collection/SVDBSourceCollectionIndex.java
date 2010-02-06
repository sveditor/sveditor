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


package net.sf.sveditor.core.db.index.src_collection;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

/* 
 * Manages the index for a workspace location
 * 
 */
public class SVDBSourceCollectionIndex 
	extends AbstractSVDBIndex implements ISVDBIncludeFileProvider {
	
	protected int								fIndexType;

	protected String							fBaseLocation;
	protected boolean							fDisposed;

	protected List<ISVDBIndexChangeListener>	fIndexChageListeners;
	
	protected List<ISVDBIncludeFileProvider>	fIncludePaths;
	
	protected SVDBFileTreeUtils					fFileTreeUtils;
	protected AbstractSVFileMatcher				fFileMatcher;
	
	public SVDBSourceCollectionIndex(
			String					project,
			String 					base_location,
			int						index_type,
			AbstractSVFileMatcher	file_matcher,
			ISVDBFileSystemProvider	fs_provider) {
		super(project, fs_provider);

		fFileMatcher = file_matcher;
		
		if (fFileMatcher == null) {
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		fBaseLocation = base_location;
		fIndexType    = index_type;
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();

		fFileTreeUtils    = new SVDBFileTreeUtils();
		fLog = LogFactory.getDefault().getLogHandle("SVDBSourceCollectionIndex");
	}
	
	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}
	
	@Override
	protected boolean isLoadUpToDate() {
		List<String> files = fFileMatcher.findIncludedPaths();
		
		if (files.size() != fFileList.size()) {
			fLog.debug("    Index not up-to-date: files.size=" + 
					files.size() + " fFileList.size=" + fFileList.size());
			return false;
		}
		
		for (String file : files) {
			SVDBFile pp_file = fFileList.get(file);
			
			if (pp_file == null ||
					(pp_file.getLastModified() != fFileSystemProvider.getLastModifiedTime(file))) {
				if (pp_file == null) {
					fLog.debug("    Index not up-to-date: file \"" +
							file + "\" not in index");
				} else {
					fLog.debug("    Index not up-to-date: file \"" +
							file + "\" cached timestamp " + pp_file.getLastModified() + 
							" filesystem timestamp " + fFileSystemProvider.getLastModifiedTime(file));
				}
				return false;
			}
		}
		
		return true;
	}

	public void dispose() {
		super.dispose();
		fDisposed = true;
	}
	
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		
		if (!fDisposed) {
			dispose();
		}
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public SVDBFile parse(InputStream in, String path) {
		SVDBFileTreeUtils utils = new SVDBFileTreeUtils();

		Map<String, SVDBFile> pp_map = getPreProcFileMap();
		
		SVDBFileTree ft = utils.createFileContext(pp_map.get(path), this);
		
		return parseFile(in, path, ft);
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		
		Iterator<String> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			String f = it.next();
			
			String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
				return new SVDBSearchResult<SVDBFile>(map.get(f), this);
			}
		}
		
		return null;
	}
	
	protected synchronized void buildPreProcFileMap() {
		try {
			SVPreProcScanner sc            = new SVPreProcScanner();
			SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
			sc.setObserver(s_observer);

			// 	Discover files
			fLog.debug("Building SourceCollection index " + fBaseLocation);
			if (fFileMatcher == null) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			for (String path : fFileMatcher.findIncludedPaths()) {
				fLog.debug("    path=" + path);
				if (fFileList.containsKey(path)) {
					fFileList.remove(path);
				}
				fFileList.put(path, createPreProcFile(path));
			}
		} catch (Exception e) { 
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileListValid = true;
			}
		}
	}
	
	private SVDBFile createPreProcFile(String file) {
		SVPreProcScanner sc            = new SVPreProcScanner();
		SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
	
		sc.setObserver(s_observer);

		InputStream in = fFileSystemProvider.openStream(file);

		if (in != null) {
			sc.init(in, file);
			sc.scan();
			fFileSystemProvider.closeStream(in);
		} else {
			fLog.error("Failed to open file \"" + file + "\" in index " + fFileSystemProvider.getClass().getName());
		}
			
		if (s_observer.getFiles().size() > 0) {
			SVDBFile svdb_f = s_observer.getFiles().get(0);
			
			svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(file));
			
			return svdb_f;
		} else {
			return null;
		}
	}
	
	protected synchronized void buildIndex() {
		fLog.debug("SourceCollectionIndex: updateFileIndex \"" + fBaseLocation + "\"");
		
		try {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();

			Iterator<String> it = pp_file_map.keySet().iterator();

			while (it.hasNext()) {
				String file = it.next();
				fLog.debug("    file=" + file);
				
				if (!fFileIndex.containsKey(file)) {
					SVDBFileTree ft = fFileTreeUtils.createFileContext(
							pp_file_map.get(file), this);
					SVDBFile svdb_file = parseFile(file, ft);
					
					synchronized(fFileIndex) {
						fFileIndex.put(file, svdb_file);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileIndexValid = true;
			}
		}
	}
	
	private SVDBFile parseFile(String file, SVDBFileTree file_tree) {
		InputStream in = fFileSystemProvider.openStream(file);
		return parseFile(in, file, file_tree);
	}

	private SVDBFile parseFile(InputStream in, String path, SVDBFileTree file_tree) {
		SVDBFile svdb_file = null;
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(fMacroProvider);
		svdb_file = SVDBFileFactory.createFile(in, path, dp);
		
		svdb_file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));

		fFileSystemProvider.closeStream(in);
		
		return svdb_file;
	}

	public int getIndexType() {
		return fIndexType;
	}

	public void rebuildIndex() {
		// TODO: force index and map to be invalid
		fLog.debug("[TODO] SVDBIndexBase.rebuildIndex");
	}
	
	public void addChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.add(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.remove(l);
	}
	
	

	protected void fileRemoved(String file) {
		fFileList.remove(file);
		SVDBFile svdb_file = fFileIndex.remove(file);

		if (svdb_file != null) {
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_REMOVED, svdb_file);
			}
		}
	}
	
	protected void fileAdded(String file) {
		// First, decide whether this is a file to ignore
		if (file.lastIndexOf('.') != -1) {
			String ext = file.substring(file.lastIndexOf('.'));
			
			if (!fSVExtensions.contains(ext)) {
				return;
			}
			
			// Next, check whether there is an ignore dir on the path
			File parent = new File(file).getParentFile();
			File last_parent = null;
			
			while (parent != null &&
					(last_parent == null || !last_parent.equals(parent))) {
				if (fIgnoreDirs.contains(parent.getName())) {
					return;
				}
				last_parent = parent;
				parent = parent.getParentFile();
			}
		} else {
			return;
		}
		
		if (fFileListValid) {
			if (fFileList.containsKey(file)) {
				// hmmm... bad information
				fFileList.remove(file);
			}
			
			fFileList.put(file, createPreProcFile(file));
		}
		
		if (fFileIndexValid) {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();
			
			if (fFileIndex.containsKey(file)) {
				fFileIndex.remove(file);
			}
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), this);
			SVDBFile svdb_file = parseFile(file, ft);
			
			synchronized(fFileIndex) {
				fFileIndex.put(file, svdb_file);
			}
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_ADDED, svdb_file);
			}
		}
	}
	
	
	protected void fileChanged(String file) {
		
		if (fFileList.containsKey(file)) {
			fFileList.remove(file);
			fFileList.put(file, createPreProcFile(file));
		}

		if (fFileIndex.containsKey(file)) {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), this);
			SVDBFile svdb_file = parseFile(file, ft);
			SVDBFile svdb_file_e = fFileIndex.get(file);

			// Merge any new content with the existing
			SVDBFileMerger.merge(svdb_file_e, svdb_file, null, null, null);
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_CHANGED, svdb_file_e);
			}
		}
	}

	private IPreProcMacroProvider fMacroProvider = new IPreProcMacroProvider() {
		Map<String, SVDBMacroDef> fMacroCache = new HashMap<String, SVDBMacroDef>();
		
		public void setMacro(String key, String value) {
			if (fMacroCache.containsKey(key)) {
				fMacroCache.get(key).setDef(value);
			} else {
				SVDBMacroDef def = new SVDBMacroDef(key, new ArrayList<String>(), value);
				fMacroCache.put(key, def);
			}
		}
		
		public SVDBMacroDef findMacro(String name, int lineno) {
			if (fMacroCache.containsKey(name)) {
				return fMacroCache.get(name);
			} else {
				SVDBMacroDef m = null;
				for (SVDBFile pp : getPreProcFileMap().values()) {
					if ((m = find_macro(name, pp)) != null) {
						break;
					}
				}
				return m;
			}
		}
		
		private SVDBMacroDef find_macro(String key, SVDBScopeItem scope) {
			for (SVDBItem it : scope.getItems()) {
				if (it.getType() == SVDBItemType.Macro && it.getName().equals(key)) {
					return (SVDBMacroDef)it;
				} else if (it instanceof SVDBScopeItem) {
					return find_macro(key, (SVDBScopeItem)it);
				}
			}
			
			return null;
		}
		
		public void addMacro(SVDBMacroDef macro) {
			if (fMacroCache.containsKey(macro.getName())) {
				fMacroCache.remove(macro.getName());
			}
			fMacroCache.put(macro.getName(), macro);
		}
	};
	
}
