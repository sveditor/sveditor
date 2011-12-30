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
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBSourceCollectionIndex extends AbstractSVDBIndex {
	
	private AbstractSVFileMatcher			fFileMatcher;
	/*
	private Set<SVDBFile>					fModIfcClsFiles;
	private Set<SVDBFile>					fUnincludedFiles;
	 */
	
	static {
		LogFactory.getLogHandle("Index.SourceCollectionIndex");
	}
	
	SVDBSourceCollectionIndex(
			String					project,
			String					root,
			AbstractSVFileMatcher	matcher,
			ISVDBFileSystemProvider	fs_provider,
			ISVDBIndexCache			cache,
			Map<String, Object>		config) {
		super(project, root, fs_provider, cache, config);
		
		fFileMatcher = matcher;
		/*
		fModIfcClsFiles = new HashSet<SVDBFile>();
		fUnincludedFiles = new HashSet<SVDBFile>();
		 */
	}
	
	@Override
	protected String getLogName() {
		return "SourceCollectionIndex";
	}



	@Override
	protected boolean checkCacheValid() {
		boolean valid = super.checkCacheValid();
		
		if (valid) {
			List<String> file_paths = fFileMatcher.findIncludedPaths();
			Set<String> cache_files = getCache().getFileList();
			List<String> tmp_cache_files = new ArrayList<String>();
			
			tmp_cache_files.addAll(cache_files);
			
			// First, check that all discovered files exist
			for (String path : file_paths) {
				if (cache_files.contains(path)) {
					long fs_timestamp = getFileSystemProvider().getLastModifiedTime(path);
					long cache_timestamp = getCache().getLastModified(path);
					
					if (cache_timestamp < fs_timestamp) {
						valid = false;
						break;
					}
					tmp_cache_files.remove(path);
				} else {
					valid = false;
					break;
				}
			}
			
			// If all discovered files are up-to-date in the cache,
			// check any cached files that were not discovered
			if (valid) {
				for (String path : tmp_cache_files) {
					if (getFileSystemProvider().fileExists(path)) {
						long fs_timestamp = getFileSystemProvider().getLastModifiedTime(path);
						long cache_timestamp = getCache().getLastModified(path);

						if (cache_timestamp < fs_timestamp) {
							valid = false;
							break;
						}
					} else {
						valid = false;
						break;
					}
				}
			}
		}
		
		return valid;
	}



	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		List<String> file_paths = fFileMatcher.findIncludedPaths();
		
		for (String path : file_paths) {
			String rp = resolvePath(path, fInWorkspaceOk);
			fLog.debug("Adding root file \"" + rp + "\"");
			addFile(rp);
			addIncludePath(SVFileUtils.getPathParent(rp));
		}
	}

	/**
	 * initPaths()
	 * 
	 * Must ensure that the file paths are discovered prior to 
	 * calling this
	 */
	/*
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
	 */

	/** TEMP
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
	 */
	
	/** TEMP
	@Override
	protected void buildIndex(IProgressMonitor monitor) {
		fLog.debug("--> buildIndex()");
		long start = System.currentTimeMillis();
		getPreProcFileMap(monitor); // force pre-proc info to be built
		
		for (SVDBFile pp_file : fModIfcClsFiles) {
			if (fFileTreeMap.get(pp_file.getFilePath()) != null) {
				dump_file_tree("ROOT", fFileTreeMap.get(pp_file.getFilePath()));
			}
		}

		for (SVDBFile pp_file : fUnincludedFiles) {
			if (fFileTreeMap.get(pp_file.getFilePath()) != null) {
				dump_file_tree("UNINC", fFileTreeMap.get(pp_file.getFilePath()));
			}
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
		
		signalIndexRebuilt();
		long end = System.currentTimeMillis();
		fLog.debug("<-- buildIndex(" + (end-start) + ")");
	}
	 */
	
	/** TEMP
	private void dump_file_tree(String type, SVDBFileTree ft) {
		if (ft == null) {
			fLog.debug("dump_file_tree: type=" + type + " ft=null");
			return;
		}
		fLog.debug(type + ": " + ft.getFilePath());
		
		for (SVDBFileTree inc : ft.getIncludedFiles()) {
			dump_down(inc, 1);
		}
	}
		 */
	
	/** TEMP
	private void dump_down(SVDBFileTree ft, int indent) {
		String indent_s;
		StringBuilder indent_sb = new StringBuilder();
		for (int i=0; i<indent; i++) {
			indent_sb.append("  ");
		}
		indent_s = indent_sb.toString();
		
		fLog.debug(indent_s + "IncFile: " + ft.getFilePath());
		for (SVDBFileTree inc : ft.getIncludedFiles()) {
			dump_down(inc, indent+1);
		}
	}
		 */
	
	@Override
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		SVDBSearchResult<SVDBFile> ret = super.findIncludedFile(path);
	
		/*
		if (ret != null) {
			if (fUnincludedFiles.contains(ret.getItem())) {
				fLog.debug("Remove include file \"" + 
						ret.getItem().getFilePath() + 
						"\" from unincluded files");
				fUnincludedFiles.remove(ret.getItem());
			}
		}
		 */

		return ret;
	}

	/*
	private boolean has_pkg_interface_module_program(ISVDBScopeItem scope) {
		if (scope.getType() == SVDBItemType.ModuleDecl ||
				scope.getType() == SVDBItemType.InterfaceDecl ||
				scope.getType() == SVDBItemType.ProgramDecl ||
				scope.getType() == SVDBItemType.PackageDecl) {
			return true;
		} else {
			for (ISVDBItemBase it : scope.getItems()) {
				if (it instanceof ISVDBScopeItem) {
					if (has_pkg_interface_module_program((ISVDBScopeItem)it)) {
						return true;
					}
				}
			}
		}
		
		return false;
	}
	 */

	/*
	public void fileAdded(String path) {
		String res_base = getResolvedBaseLocation();
		
		if (path.startsWith(res_base)) {
			rebuildIndex();
		}
	}

	public void fileRemoved(String path) {
		// if (fPreProcFileMap.containsKey(path)) {
		//	rebuildIndex();
		// }
	}
	 */

	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}
	
}
