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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;

public class SVDBSourceCollectionIndex extends SVDBLibIndex {
	
	private AbstractSVFileMatcher			fFileMatcher;
	private List<String>					fFilePaths;
	private Set<SVDBFile>					fModIfcClsFiles;
	private Set<SVDBFile>					fUnincludedFiles;
	
	static {
		LogFactory.getLogHandle("Index.SourceCollectionIndex");
	}
	
	SVDBSourceCollectionIndex(
			String					project,
			String					root,
			AbstractSVFileMatcher	matcher,
			ISVDBFileSystemProvider	fs_provider) {
		super(project, root, fs_provider);
		
		fLog = LogFactory.getLogHandle("Index.SourceCollectionIndex");
		
		fFileMatcher = matcher;
		fModIfcClsFiles = new HashSet<SVDBFile>();
		fUnincludedFiles = new HashSet<SVDBFile>();
	}
	
	@Override
	public void load(
			IDBReader 		index_data, 
			List<SVDBFile> 	pp_files,
			List<SVDBFile> 	db_files) throws DBFormatException {
		load_base(index_data, pp_files, db_files);

		if (isLoaded()) {
			fFilePaths = fFileMatcher.findIncludedPaths();
			
			for (int i=0; i<fFilePaths.size(); i++) {
				fFilePaths.set(i, SVFileUtils.normalize(fFilePaths.get(i)));
			}
			
			initPaths();
			loadMarkers();

			// re-build the FileTree structure
			for (String path : fFilePaths) {
				SVDBFile pp_file = processPreProcFile(path, true);
				if (has_pkg_interface_module_program(pp_file)) {
					fModIfcClsFiles.add(pp_file);
				} else {
					fUnincludedFiles.add(pp_file);
				}
			}
			
			for (SVDBFile pp_file : fModIfcClsFiles) {
				fLog.debug("Process top-level file: " + pp_file.getFilePath());
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}

			// Finally, add the files that weren't included
			for (SVDBFile pp_file : fUnincludedFiles) {
				fLog.debug("Process un-included file: " + pp_file.getFilePath());
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}
		}
	}
	
	/**
	 * initPaths()
	 * 
	 * Must ensure that the file paths are discovered prior to 
	 * calling this
	 */
	@Override
	protected void initPaths() {
		// Update the include-paths list
		for (String path : fFilePaths) {
			String inc_dir = SVFileUtils.getPathParent(path);
			if (!fIncludePaths.contains(inc_dir)) {
				fIncludePaths.add(inc_dir);
			}
		}
	}

	@Override
	protected synchronized void buildPreProcFileMap() {
		// Say the index is already valid
		fPreProcFileMapValid = true;
		
		fFilePaths = fFileMatcher.findIncludedPaths();
		for (int i=0; i<fFilePaths.size(); i++) {
			fFilePaths.set(i, SVFileUtils.normalize(fFilePaths.get(i)));
		}
		
		initPaths();
		
		// Create the pre-processed files
		for (String path : fFilePaths) {
			SVDBFile pp_file = processPreProcFile(path, true);
			if (has_pkg_interface_module_program(pp_file)) {
				fLog.debug("Adding \"" + pp_file.getFilePath() + "\" to ModIfc files");
				fModIfcClsFiles.add(pp_file);
			} else {
				fUnincludedFiles.add(pp_file);
			}
		}
		
		for (SVDBFile pp_file : fModIfcClsFiles) {
			fLog.debug("Process top-level file: " + pp_file.getFilePath());
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}

		// Finally, add the files that weren't included
		Set<SVDBFile> tmp = new HashSet<SVDBFile>();
		tmp.addAll(fUnincludedFiles);
		
		for (SVDBFile pp_file : tmp) {
			fLog.debug("Process un-included file: " + pp_file.getFilePath());
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}
	
	@Override
	protected void buildIndex() {
		fLog.debug("--> buildIndex()");
		long start = System.currentTimeMillis();
		getPreProcFileMap(); // force pre-proc info to be built
		
		for (SVDBFile pp_file : fModIfcClsFiles) {
			dump_file_tree("ROOT", fFileTreeMap.get(pp_file.getFilePath()));
		}

		for (SVDBFile pp_file : fUnincludedFiles) {
			dump_file_tree("UNINC", fFileTreeMap.get(pp_file.getFilePath()));
		}

		for (SVDBFile pp_file : fModIfcClsFiles) {
			SVDBFileTree ft_root = fFileTreeMap.get(pp_file.getFilePath());

			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			processFile(ft_root, mp);
		}

		for (SVDBFile pp_file : fUnincludedFiles) {
			SVDBFileTree ft_root = fFileTreeMap.get(pp_file.getFilePath());

			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			processFile(ft_root, mp);
		}

		fIndexFileMapValid = true;
		
		long end = System.currentTimeMillis();
		fLog.debug("<-- buildIndex(" + (end-start) + ")");
	}
	
	private void dump_file_tree(String type, SVDBFileTree ft) {
		fLog.debug(type + ": " + ft.getFilePath());
		
		for (SVDBFileTree inc : ft.getIncludedFiles()) {
			dump_down(inc, 1);
		}
	}
	
	private void dump_down(SVDBFileTree ft, int indent) {
		String indent_s = "";
		for (int i=0; i<indent; i++) {
			indent_s += "  ";
		}
		
		fLog.debug(indent_s + "IncFile: " + ft.getFilePath());
		for (SVDBFileTree inc : ft.getIncludedFiles()) {
			dump_down(inc, indent+1);
		}
	}
	
	@Override
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		SVDBSearchResult<SVDBFile> ret = super.findIncludedFile(path);
	
		if (ret != null) {
			if (fUnincludedFiles.contains(ret.getItem())) {
				fLog.debug("Remove include file \"" + 
						ret.getItem().getFilePath() + 
						"\" from unincluded files");
				fUnincludedFiles.remove(ret.getItem());
			}
		}

		return ret;
	}

	private boolean has_pkg_interface_module_program(SVDBScopeItem scope) {
		if (scope.getType() == SVDBItemType.Module ||
				scope.getType() == SVDBItemType.Interface ||
				scope.getType() == SVDBItemType.Program ||
				scope.getType() == SVDBItemType.PackageDecl) {
			return true;
		} else {
			for (SVDBItem it : scope.getItems()) {
				if (it instanceof SVDBScopeItem) {
					if (has_pkg_interface_module_program((SVDBScopeItem)it)) {
						return true;
					}
				}
			}
		}
		
		return false;
	}

	@Override
	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}
	
	@Override
	public String getTypeName() {
		return "SourceCollectionIndex";
	}

}
