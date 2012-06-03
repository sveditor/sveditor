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
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBSourceCollectionIndex extends AbstractSVDBIndex {
	
	private List<AbstractSVFileMatcher>		fFileMatcherList;
	/*
	private Set<SVDBFile>					fModIfcClsFiles;
	private Set<SVDBFile>					fUnincludedFiles;
	 */
	
	static {
		LogFactory.getLogHandle("Index.SourceCollectionIndex");
	}
	
	SVDBSourceCollectionIndex(
			String							project,
			String							root,
			List<AbstractSVFileMatcher>		matcher_list,
			ISVDBFileSystemProvider			fs_provider,
			ISVDBIndexCache					cache,
			SVDBIndexConfig					config) {
		super(project, root, fs_provider, cache, config);
		
		fFileMatcherList = matcher_list;
	}
	
	@Override
	protected String getLogName() {
		return "SourceCollectionIndex";
	}

	@Override
	protected boolean checkCacheValid() {
		boolean valid = super.checkCacheValid();
		
		if (valid) {
			for (int i=0; i<fFileMatcherList.size(); i++) {
				AbstractSVFileMatcher matcher = fFileMatcherList.get(i);
				List<String> file_paths = matcher.findIncludedPaths();
				Set<String> cache_files = getCache().getFileList();
				List<String> tmp_cache_files = new ArrayList<String>();

				tmp_cache_files.addAll(cache_files);

				// First, check that all discovered files exist
				for (String path : file_paths) {
					if (cache_files.contains(path)) {
						long fs_timestamp = getFileSystemProvider().getLastModifiedTime(path);
						long cache_timestamp = getCache().getLastModified(path);

						if (cache_timestamp < fs_timestamp) {
							if (fDebugEn) {
								fLog.debug(LEVEL_MIN, "Cache is invalid due to timestamp on " + path +
										": file=" + fs_timestamp + " cache=" + cache_timestamp);
							}
							valid = false;
							break;
						}
						tmp_cache_files.remove(path);
					} else {
						if (fDebugEn) {
							fLog.debug(LEVEL_MIN, "Cache is invalid due to uncached file " + path);
						}
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
								if (fDebugEn) {
									fLog.debug(LEVEL_MIN, "Cache is invalid due to timestamp on " + path +
											": file=" + fs_timestamp + " cache=" + cache_timestamp);
								}
								valid = false;
								break;
							}
						} else {
							if (fDebugEn) {
								fLog.debug(LEVEL_MIN, "Cache is invalid due to uncached file " + path);
							}
							valid = false;
							break;
						}
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "[SVDBSourceCollectionIndex] Cache is " + ((valid)?"valid":"invalid"));
		}
		return valid;
	}



	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		for (int i=0; i<fFileMatcherList.size(); i++) {
			AbstractSVFileMatcher matcher = fFileMatcherList.get(i);
			List<String> file_paths = matcher.findIncludedPaths();
			
			fLog.debug(LEVEL_MIN, "discoverRootFiles");
			
			for (String path : file_paths) {
				String rp = resolvePath(path, fInWorkspaceOk);
				fLog.debug(LEVEL_MID, "Adding root file \"" + rp + "\"");
				addFile(rp);
				addIncludePath(SVFileUtils.getPathParent(rp));
			}
		}
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
