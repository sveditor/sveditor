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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBLibIndex extends AbstractSVDBIndex implements ISVDBFileSystemChangeListener {
	protected Map<String, SVDBFileTree>		fFileTreeMap;
	protected String						fRoot;
	protected String						fResolvedRoot;
	protected SVPreProcDefineProvider		fDefineProvider;

	
	public SVDBLibIndex(
			String 					project, 
			String 					root,
			ISVDBFileSystemProvider fs_provider) {
		super(project, fs_provider);
		
		fDefineProvider = new SVPreProcDefineProvider(null);
		fFileTreeMap 	= new HashMap<String, SVDBFileTree>();
		fRoot 			= root;
		fResolvedRoot	= expandVars(fRoot, true);
		fLog = LogFactory.getDefault().getLogHandle("SVDBLibIndex");
		
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
			fResolvedRoot = expandVars(fRoot, true);
		}
		
		return fResolvedRoot;
	}
	
	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}

	public void rebuildIndex() {
		fLog.debug("rebuildIndex \"" + getBaseLocation() + "\"");
		fFileIndex.clear();
		fFileList.clear();
		fFileTreeMap.clear();
		
		fFileIndexValid = false;
		fFileListValid  = false;
	}
	
	public void load(
			IDBReader index_data, 
			List<SVDBFile> ppFiles, 
			List<SVDBFile> dbFiles) throws DBFormatException {
		load_base(index_data, ppFiles, dbFiles);
		
		if (fFileIndexValid && fFileListValid) {
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
		
		Map<String, SVDBFile> pp_map = fFileList; // FileMap in progress
		
		if (pp_map.containsKey(inc_path)) {
			fLog.debug("findIncludedFile: \"" + inc_path + "\" already in map");
			return new SVDBSearchResult<SVDBFile>(pp_map.get(inc_path), this);
		} else {
			SVDBFile pp_file = null;
			
			if (fFileSystemProvider.fileExists(inc_path)) {
				fLog.debug("findIncludedFile: building entry for \"" + inc_path + "\"");
				
				pp_file = processPreProcFile(inc_path);
			
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
		for (SVDBFile svdb_f : fFileList.values()) {
			String path = svdb_f.getFilePath();
			
			if (!fFileSystemProvider.fileExists(path) ||  
					(svdb_f.getLastModified() != fFileSystemProvider.getLastModifiedTime(path))) {
				debug("    file \"" + path + "\": saved timestamp: " +
						svdb_f.getLastModified() + " ; current timestamp: " + 
						fFileSystemProvider.getLastModifiedTime(path));
				return false;
			}
		}
		
		return true;
	}
	

	public SVDBFile parse(InputStream in, String path) {
		SVDBFileFactory scanner = new SVDBFileFactory(fDefineProvider);
		
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
		}
		
		if (file_tree != null) {
			fDefineProvider.setMacroProvider(new SVFileTreeMacroProvider(file_tree));
			SVDBFile svdb_f = scanner.parse(in, file_tree.getFilePath());
			svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
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
		fFileListValid = true;

		SVDBFile pp_file = processPreProcFile(getResolvedBaseLocation());

		if (pp_file == null) {
			fLog.error("buildPreProcFileMap: Failed to find file \"" + 
					getResolvedBaseLocation() + "\"");
			return;
		}
		
		
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		buildPreProcFileMap(null, ft_root);
		
		fFileListValid = true;
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
		
		ft_utils.resolveConditionals(root);
		
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
			fFileIndexValid = true;
			return;
		}

		SVDBFileTree ft_root = fFileTreeMap.get(getResolvedBaseLocation());
		
		SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(ft_root);
		processFile(ft_root, mp);
		
		fFileIndexValid = true;
		
		long end = System.currentTimeMillis();
		fLog.debug("<-- buildIndex(" + (end-start) + ")");
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
		
		if (fFileList.containsKey(file.getFilePath())) {
			fFileList.remove(file.getFilePath());
		}
		fFileList.put(file.getFilePath(), file);

		file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));
		
		return file;
	}

	protected void processFile(
			SVDBFileTree				path,
			SVFileTreeMacroProvider 	mp) {
		
		if (path.getFilePath().indexOf("xbus_master_seq_lib.sv") != -1) {
			dumpUp(path);
		}
		
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
		
		if (fFileIndex.containsKey(path.getFilePath())) {
			// Merge the files together. This happens during an update
			SVDBFile existing = fFileIndex.get(path.getFilePath());
			SVDBFileMerger.merge(existing, svdb_f, null, null, null);
			existing.setLastModified(svdb_f.getLastModified());
		} else {
			// Just add the file. This happens on first parse
			fFileIndex.put(path.getFilePath(), svdb_f);
		}

		// Now, recurse through the files included
		for (SVDBFileTree ft_t : path.getIncludedFiles()) {
			// Note: process files that are currently not in the FileIndex, 
			// but are in the pre-processor list. This ensures that we 
			// don't try to process files included from another index
			if (!fFileIndex.containsKey(ft_t.getFilePath()) &&
					fFileList.containsKey(ft_t.getFilePath())) {
				mp = new SVFileTreeMacroProvider(ft_t);
				processFile(ft_t, mp);
			}
		}

		fFileSystemProvider.closeStream(in);
	}

	protected void addIncludeFiles(
			SVDBFileTree 		root, 
			SVDBScopeItem 		scope) {
		for (SVDBItem it : scope.getItems()) {
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
					fLog.error("AbstractSVDBLibIndex: " +
							getBaseLocation() + " failed to find include file " + it.getName());
				}
				
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
	
	public void fileAdded(String path) {
		// fileAdded is ignored for LibIndex, since all the
		// files are explicitly specified
	}

	public void fileChanged(String path) {
		
		if (fFileListValid && fFileList.containsKey(path)) {
			fLog.debug("fileChanged: " + path);
			// Rescan the file
			SVDBFile orig_file = fFileList.get(path);
			SVDBFile pp_file = processPreProcFile(path);

			// Merge the new content to the existing content
			SVDBFileMerger.merge(orig_file, pp_file, null, null, null);
			orig_file.setLastModified(pp_file.getLastModified());
			SVDBFileTree ft = fFileTreeMap.get(path);
			ft.setSVDBFile(pp_file);
			
			// Update the pre-processor map
			buildPreProcFileMap(null, ft);

			if (fFileIndexValid && fFileIndex.containsKey(path)) {
				// rebuild the index
				SVDBFileTree ft_root = fFileTreeMap.get(path);
				SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(ft_root);
				
				processFile(ft_root, mp);
			}
		}
	}
	
	private void dumpUp(SVDBFileTree ft) {
		if (ft.getIncludedByFiles().size() > 0) {
			dumpUp(ft.getIncludedByFiles().get(0));
		} else {
			fLog.debug("Top FileTree: " + ft.getFilePath());
			for (SVDBFileTree ft_s : ft.getIncludedFiles()) {
				dumpDown(1, ft_s);
			}
		}
	}
	
	private void dumpDown(int indent, SVDBFileTree ft) {
		String ind_s = "";
		for (int i=0; i<indent; i++) {
			ind_s += "    ";
		}
		fLog.debug(ind_s + "Include \"" + ft.getFilePath() + "\"");
		for (SVDBFileTree ft_s : ft.getIncludedFiles()) {
			dumpDown(indent+1, ft_s);
		}
	}

	public void fileRemoved(String path) {
		if (fFileListValid && fFileList.containsKey(path)) {
			fLog.debug("fileRemoved: \"" + path + "\"");
			fFileList.remove(path);
			fFileTreeMap.remove(path);
			fFileIndex.remove(path);
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
