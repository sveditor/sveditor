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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBLibIndex extends AbstractSVDBIndex implements ISVDBFileSystemChangeListener {
	protected Map<String, SVDBFileTree>				fFileTreeMap;
	protected String								fRoot;
	protected String								fResolvedRoot;
	protected SVPreProcDefineProvider				fDefineProvider;
	protected Map<String, List<SVDBMarkerItem>>		fMarkerMap;
	
	public SVDBLibIndex(
			String 					project, 
			String 					root,
			ISVDBFileSystemProvider fs_provider) {
		super(project, fs_provider);
		
		fDefineProvider = new SVPreProcDefineProvider(null);
		fFileTreeMap 	= new HashMap<String, SVDBFileTree>();
		fRoot 			= root;
		fResolvedRoot	= SVDBIndexUtil.expandVars(fRoot, true);
		fLog = LogFactory.getLogHandle("SVDBLibIndex");
		
		fMarkerMap = new HashMap<String, List<SVDBMarkerItem>>();
		
		// Initialize the filesystem interface
		if (fFileSystemProvider != null) {
			fFileSystemProvider.init(fResolvedRoot);
			fFileSystemProvider.addFileSystemChangeListener(this);
		}
	}
	
	public String getTypeID() {
		return SVDBLibPathIndexFactory.TYPE;
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}
	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	
	public String getBaseLocation() {
		return fRoot;
	}
	
	public String getResolvedBaseLocation() {

		if (fResolvedRoot == null) {
			fResolvedRoot = SVDBIndexUtil.expandVars(fRoot, true);
		}
		
		return fResolvedRoot;
	}
	
	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}

	public void rebuildIndex() {
		fLog.debug("rebuildIndex \"" + getBaseLocation() + "\"");
		fIndexFileMap.clear();
		fPreProcFileMap.clear();
		fFileTreeMap.clear();
		
		fIndexFileMapValid = false;
		fPreProcFileMapValid  = false;
	}
	
	public void load(
			IDBReader index_data, 
			List<SVDBFile> ppFiles, 
			List<SVDBFile> dbFiles) throws DBFormatException {
		load_base(index_data, ppFiles, dbFiles);
		
		if (fIndexFileMapValid && fPreProcFileMapValid) {
			fMarkerMap.clear();
			
			// Add in the markers
			for (SVDBFile f : fIndexFileMap.values()) {
				List<SVDBMarkerItem> marker_list = null;
				
				for (SVDBItem it : f.getItems()) {
					if (it.getType() == SVDBItemType.Marker) {
						if (marker_list == null) {
							marker_list = new ArrayList<SVDBMarkerItem>();
						}
						marker_list.add((SVDBMarkerItem)it);
					}
				}
			}
			SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}

	/**
	 * findIncludedFile()
	 * 
	 * Search the include paths within this index
	 */
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		String root_dir = new File(getResolvedBaseLocation()).getParent();
		String inc_path = root_dir + "/" + path;
		
		fLog.debug("inc_path=\"" + inc_path + "\"");
		
		Map<String, SVDBFile> pp_map = fPreProcFileMap; // FileMap in progress
		
		if (pp_map.containsKey(inc_path)) {
			fLog.debug("findIncludedFile: \"" + inc_path + "\" already in map");
			return new SVDBSearchResult<SVDBFile>(pp_map.get(inc_path), this);
		} else {
			SVDBFile pp_file = null;
			
			if (fFileSystemProvider.fileExists(inc_path)) {
				fLog.debug("findIncludedFile: building entry for \"" + inc_path + "\"");
				
				pp_file = processPreProcFile(inc_path, true);
			
			} else {
				fLog.debug("findIncludedFile: file \"" + inc_path + "\" does not exist");
			}
			
			if (pp_file != null) {
				return new SVDBSearchResult<SVDBFile>(pp_file, this);
			} else {
				return null;
			}
		}
	}
	
	@Override
	protected boolean isLoadUpToDate() {
		
		// Now, iterate through and check lastModified timestamps
		for (SVDBFile svdb_f : fPreProcFileMap.values()) {
			String path = svdb_f.getFilePath();
			
			if (!fFileSystemProvider.fileExists(path) ||  
					(svdb_f.getLastModified() != fFileSystemProvider.getLastModifiedTime(path))) {
				debug("    file \"" + path + "\": saved timestamp: " +
						svdb_f.getLastModified() + " ; current timestamp: " + 
						fFileSystemProvider.getLastModifiedTime(path));
				return false;
			}
		}
		
		// Now, collect all missing include files. Rebuild if any exist
		Map<SVDBFile, List<String>> missing_inc = find_missing_inc_svdb();
		for (Entry<SVDBFile, List<String>> entry : missing_inc.entrySet()) {
			for (String inc : entry.getValue()) {
				SVDBSearchResult<SVDBFile> inc_svdb = findIncludedFile(inc);
				
				if (inc_svdb != null) {
					// Found the include, so rebuild
					return false;
				}
			}
		}
		
		return true;
	}
	
	private void find_foo(SVDBScopeItem parent) {
		for (SVDBItem it : parent.getItems()) {
			if (it instanceof SVDBScopeItem) {
				find_foo((SVDBScopeItem)it);
			} else if (it.getType() == SVDBItemType.Macro) {
				if (it.getName().startsWith("foo")) {
					fLog.debug("Macro \"" + it.getName() + "\" defined");
				}
			}
		}
	}

	public SVDBFile parse(InputStream in, String path) {
		SVDBFileFactory scanner = new SVDBFileFactory(fDefineProvider);
		
		InputStreamCopier copier = new InputStreamCopier(in);
		in = null;
		
		getFileDB();
		
		SVDBFileTree file_tree = fFileTreeMap.get(path);
		
		if (file_tree == null) {
			fLog.error("File \"" + path + "\" not in FileTreeMap of " + getResolvedBaseLocation());
			for (SVDBFileTree ft : fFileTreeMap.values()) {
				fLog.debug("    " + ft.getFilePath());
			}
			
			// Create an entry if possible
			SVDBFile svdb_f = findPreProcFile(path);
			
			if (svdb_f != null) {
				file_tree = new SVDBFileTree((SVDBFile)svdb_f.duplicate());
			} else {
				fLog.error("Failed to find pre-proc file \"" + path + "\" during parse()");
			}
		} else {
			SVPreProcScanner 	sc = new SVPreProcScanner();
			SVDBPreProcObserver ob = new SVDBPreProcObserver();
			sc.setObserver(ob);
			
			file_tree = file_tree.duplicate();
			
			sc.init(copier.copy(), path);
			sc.scan();
			
			SVDBFile svdb_f = ob.getFiles().get(0);
			
			for (SVDBItem it : file_tree.getSVDBFile().getItems()) {
				if (it.getType() == SVDBItemType.Marker) {
					SVDBMarkerItem m = (SVDBMarkerItem)it;
					String type = (m.getName().equals(SVDBMarkerItem.MARKER_ERR))?
							ISVDBFileSystemProvider.MARKER_TYPE_ERROR:
							ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
					fFileSystemProvider.addMarker(file_tree.getFilePath(), 
							type, m.getLocation().getLine(), m.getMessage());
				}
			}
			
			fLog.debug("Processed pre-proc file");
			
			find_foo(svdb_f);
			file_tree.setSVDBFile(svdb_f);
		}
		
		if (file_tree != null) {
			fDefineProvider.setMacroProvider(createMacroProvider(file_tree));
			SVDBFile svdb_f = scanner.parse(copier.copy(), file_tree.getFilePath());
			svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
			
			fFileSystemProvider.clearMarkers(path);
			
			for (SVDBItem it : svdb_f.getItems()) {
				if (it.getType() == SVDBItemType.Marker) {
					SVDBMarkerItem m = (SVDBMarkerItem)it;
					String type = (m.getName().equals(SVDBMarkerItem.MARKER_ERR))?
							ISVDBFileSystemProvider.MARKER_TYPE_ERROR:
							ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
					fFileSystemProvider.addMarker(path, 
							type, m.getLocation().getLine(), m.getMessage());
				}
			}
			
			
			return svdb_f;
		} else {
			debug("path \"" + path + "\" not in FileTree map");
			for (SVDBFileTree ft : fFileTreeMap.values()) {
				debug("    " + ft.getFilePath());
			}
			return null;
		}
	}
	
	/**
	 * buildPreProcFileMap()
	 * 
	 * Creating the pre-processor map requires that we build the
	 * 
	 */
	protected void buildPreProcFileMap() {
		fLog.debug("buildPreProcFileMap()");
		
		// Say the index is valid for now
		fPreProcFileMapValid = true;

		SVDBFile pp_file = processPreProcFile(getResolvedBaseLocation(), true);

		if (pp_file == null) {
			fLog.error("buildPreProcFileMap: Failed to find file \"" + 
					getResolvedBaseLocation() + "\"");
			return;
		}
		
		
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		buildPreProcFileMap(null, ft_root);
		
		fPreProcFileMapValid = true;
	}
	
	/**
	 * Recurse through included files
	 * 
	 * @param parent
	 * @param root		-- 
	 * @param file
	 */
	protected void buildPreProcFileMap(
			SVDBFileTree 	parent,
			SVDBFileTree 	root) {
		SVDBFileTreeUtils	ft_utils = new SVDBFileTreeUtils();
		SVDBFile			file = root.getSVDBFile();
		

		if (parent != null) {
			root.getIncludedByFiles().add(parent);
		}
		
		ft_utils.resolveConditionals(root, 
				new SVPreProcDefineProvider(createPreProcMacroProvider(root)));
		
		if (fFileTreeMap.containsKey(file.getFilePath())) {
			fFileTreeMap.remove(file.getFilePath());
		}
		fFileTreeMap.put(file.getFilePath(), root);
		
		addIncludeFiles(root, root.getSVDBFile());
	}
	
	/**
	 * buildIndex()
	 * 
	 * Called by AbstractSVDBIndex to build the index
	 */
	protected void buildIndex() {
		fLog.debug("--> buildIndex()");
		long start = System.currentTimeMillis();
		getPreProcFileMap(); // force pre-proc info to be built
		
		SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());

		if (pp_file == null) {
			fLog.error("Failed to find file \"" + getResolvedBaseLocation() + "\"");
			
			for (SVDBFile f : getPreProcFileMap().values()) {
				fLog.error("        " + f.getFilePath());
			}
			fIndexFileMapValid = true;
			return;
		}

		SVDBFileTree ft_root = fFileTreeMap.get(getResolvedBaseLocation());
		
		IPreProcMacroProvider mp = createMacroProvider(ft_root);
		processFile(ft_root, mp);
		
		fIndexFileMapValid = true;
		
		long end = System.currentTimeMillis();
		fLog.debug("<-- buildIndex(" + (end-start) + ")");
	}
	
	protected SVDBFile processPreProcFile(String path, boolean replace) {
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
		
		if (replace) {
			if (fPreProcFileMap.containsKey(file.getFilePath())) {
				fPreProcFileMap.remove(file.getFilePath());
			}
			fPreProcFileMap.put(file.getFilePath(), file);
		}

		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		
		return file;
	}

	protected void processFile(
			SVDBFileTree				path,
			IPreProcMacroProvider 		mp) {
		
		fDefineProvider.setMacroProvider(mp);
		SVDBFileFactory scanner = new SVDBFileFactory(fDefineProvider);
		
		String path_s = path.getFilePath();

		InputStream in = fFileSystemProvider.openStream(path_s);
		
		
		if (in == null) {
			fLog.error("Failed to open file \"" + path_s + "\"");
		}
		BufferedInputStream in_b = new BufferedInputStream(in);

		SVDBFile svdb_f = scanner.parse(in_b, path.getFilePath());
		
		svdb_f.setLastModified(
				fFileSystemProvider.getLastModifiedTime(path.getFilePath()));
		
		fFileSystemProvider.clearMarkers(path_s);
		
		// Reflect markers from pre-processor to index database
		SVDBFile svdb_pp = findPreProcFile(path_s);
		for (SVDBItem it : svdb_pp.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				svdb_f.addItem(it);
			}
		}
		
		for (SVDBItem it : svdb_f.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				String type = (m.getName().equals(SVDBMarkerItem.MARKER_ERR))?
						ISVDBFileSystemProvider.MARKER_TYPE_ERROR:
						ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
				fFileSystemProvider.addMarker(path_s, 
						type, m.getLocation().getLine(), m.getMessage());
			}
		}
		
		for (SVDBItem it : path.getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				String type = (m.getName().equals(SVDBMarkerItem.MARKER_ERR))?
						ISVDBFileSystemProvider.MARKER_TYPE_ERROR:
						ISVDBFileSystemProvider.MARKER_TYPE_WARNING;
				fFileSystemProvider.addMarker(path_s, 
						type, m.getLocation().getLine(), m.getMessage());
			}
		}
		
		if (fIndexFileMap.containsKey(path.getFilePath())) {
			// Merge the files together. This happens during an update
			SVDBFile existing = fIndexFileMap.get(path.getFilePath());
			SVDBFileMerger.merge(existing, svdb_f, null, null, null);
			existing.setLastModified(svdb_f.getLastModified());
		} else {
			// Just add the file. This happens on first parse
			fIndexFileMap.put(path.getFilePath(), svdb_f);
		}

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

		fFileSystemProvider.closeStream(in);
	}

	protected void addIncludeFiles(
			SVDBFileTree 		root,
			SVDBScopeItem 		scope) {
		for (int i=0; i<scope.getItems().size(); i++) {
			SVDBItem it = scope.getItems().get(i);

			if (it.getType() == SVDBItemType.Include) {
				fLog.debug("Include file: " + it.getName());
				
				// Look local first
				SVDBSearchResult<SVDBFile> f = findIncludedFileGlobal(it.getName());
				
				if (f != null) {
					fLog.debug("Found include file \"" + it.getName() + "\" in index \"" + 
							f.getIndex().getBaseLocation() + "\"");
					SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.getItem().duplicate());
					root.getIncludedFiles().add(ft);
					buildPreProcFileMap(root, ft);
				} else {
					SVDBFileTree ft = new SVDBFileTree(it.getName());
					root.getIncludedFiles().add(ft);
					ft.getIncludedByFiles().add(root);
					
					// Create a marker for the missing include file
					SVDBFile real_svdb = fPreProcFileMap.get(root.getFilePath());
					SVDBMarkerItem err = new SVDBMarkerItem(SVDBMarkerItem.MARKER_ERR,
							SVDBMarkerItem.KIND_MISSING_INC,
							"Failed to find include file \"" + it.getName() + "\"");
					err.setAttr(SVDBMarkerItem.MISSING_INC_PATH, it.getName());
					real_svdb.addItem(err);
					err.setLocation(it.getLocation());
					
					/*
					fLog.error("AbstractSVDBLibIndex: " +
							getBaseLocation() + " failed to find include file " + it.getName());
					 */
				}
				
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
	
	public void fileAdded(String path) {
		// fileAdded is ignored for LibIndex, since all the
		// files are explicitly specified
		int ext_idx;
		
		if ((ext_idx = path.lastIndexOf('.')) != -1) {
			// Check the missing-include paths to see if this file could match
			String ext = path.substring(ext_idx);
			
			if (fSVExtensions.contains(ext)) {
				Map<SVDBFileTree, List<String>> missing_inc = find_missing_inc();
				String last_path_elem = new File(path).getName();
				boolean found = false;
				
				for (Entry<SVDBFileTree, List<String>> entry : missing_inc.entrySet()) {
					for (String inc : entry.getValue()) {
						String inc_name = new File(inc).getName();
						
						if (last_path_elem.equals(inc_name)) {
							found = true;
							break;
						}
					}
				}
				
				// Desired outcome is a set of files that must be reprocessed 
				// to deal with this change. For now, we'll just invalidate 
				// the entire index
				if (found) {
					fLog.debug("Invalidating index");
					rebuildIndex();
				}
			}
		}
	}

	public void fileChanged(String path) {
		
		if (fPreProcFileMapValid && fPreProcFileMap.containsKey(path)) {
			fLog.debug("fileChanged: " + path);
			// Rescan the file
			SVDBFile orig_file = fPreProcFileMap.get(path);
			SVDBFile pp_file = processPreProcFile(path, true);

			// Merge the new content to the existing content
			SVDBFileMerger.merge(orig_file, pp_file, null, null, null);
			orig_file.setLastModified(pp_file.getLastModified());
			SVDBFileTree ft = fFileTreeMap.get(path);
			ft.setSVDBFile(pp_file);
			
			// Update the pre-processor map
			buildPreProcFileMap(null, ft);

			if (fIndexFileMapValid && fIndexFileMap.containsKey(path)) {
				// rebuild the index
				SVDBFileTree ft_root = fFileTreeMap.get(path);
				IPreProcMacroProvider mp = createMacroProvider(ft_root);
				
				processFile(ft_root, mp);
			}
		} else {
		}
	}
	
	private Map<SVDBFileTree, List<String>> find_missing_inc() {
		Map<SVDBFileTree, List<String>> ret = new HashMap<SVDBFileTree, List<String>>();
		
		for (SVDBFileTree ft : fFileTreeMap.values()) {
			for (SVDBFileTree inc : ft.getIncludedFiles()) {
				if (inc.getSVDBFile() == null) {
					if (!ret.containsKey(ft)) {
						ret.put(ft, new ArrayList<String>());
					}
					ret.get(ft).add(inc.getFilePath());
				}
			}
		}
		
		return ret;
	}

	private Map<SVDBFile, List<String>> find_missing_inc_svdb() {
		Map<SVDBFile, List<String>> ret = new HashMap<SVDBFile, List<String>>();
		
		for (SVDBFile ft : fPreProcFileMap.values()) {
			for (SVDBItem it : ft.getItems()) {
				if (it.getType() == SVDBItemType.Marker) {
					SVDBMarkerItem m = (SVDBMarkerItem)it;
					
					if (m.getKind().equals(SVDBMarkerItem.KIND_MISSING_INC)) {
						if (!ret.containsKey(ft)) {
							ret.put(ft, new ArrayList<String>());
						}
						ret.get(ft).add(m.getAttr(SVDBMarkerItem.MISSING_INC_PATH));
					}
				}
			}
		}
		
		return ret;
	}

	public void fileRemoved(String path) {
		if (fPreProcFileMapValid && fPreProcFileMap.containsKey(path)) {
			fLog.debug("fileRemoved: \"" + path + "\"");
			rebuildIndex();
			/*
			fPreProcFileMap.remove(path);
			fFileTreeMap.remove(path);
			fIndexFileMap.remove(path);
			 */
		}
	}

	public SVDBFile findPreProcFile(String path) {
		debug("findPreProcFile \"" + path + "\"");
		return getPreProcFileMap().get(path);
	}
	
	private void debug(String msg) {
		fLog.debug(msg);
	}

}
