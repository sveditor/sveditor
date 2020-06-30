/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.preproc;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTreeMacroList;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;

public class SVPathPreProcIncFileProvider implements ISVPreProcIncFileProvider {
	private List<String>				fIncDirs;
	
	// Map of leaf file to resolved include directory
	private Map<String, String>			fIncludeMap;
	private List<String>				fResolvedIncDirs;
	private List<Set<String>>			fIncDirFiles;
	private List<Set<String>>			fIncDirDirs;
	private Set<String>					fFailedSearches;
	private ISVDBFileSystemProvider		fFSProvider;
	private boolean						fIncludeCacheValid = false;
	
	public SVPathPreProcIncFileProvider(ISVDBFileSystemProvider fs_provider) {
		fFSProvider = fs_provider;
		fIncDirs = new ArrayList<String>();
		fIncludeMap = new HashMap<String, String>();
		fResolvedIncDirs = new ArrayList<String>();
		fIncDirFiles = new ArrayList<Set<String>>();
		fIncDirDirs = new ArrayList<Set<String>>();
		fFailedSearches = new HashSet<String>();
	}
	
	public void addIncdir(String dir) {
		if (!fIncDirs.contains(dir)) {
			fIncDirs.add(dir);
			fIncludeCacheValid = false;
		}
	}
	
	public Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(String incfile) {
		return null;
	}
	
	@Override
	public void addCachedIncFile(String incfile, String rootfile) { }

	public Tuple<String, InputStream> findIncFile(String incfile) {
		Tuple<String, InputStream> ret = null;
		
		if (!fIncludeCacheValid) {
			buildIncludeCache();
		}
		
		if (fIncludeMap.containsKey(incfile)) {
			// Already have a candidate
			String path = fIncludeMap.get(incfile) + "/" + incfile;
			InputStream in = fFSProvider.openStream(path);
			ret = new Tuple<String, InputStream>(path, in);
		} else if (!fFailedSearches.contains(incfile)) {
			// Need to look a bit harder, then. Could be a include-relative path
			String first_elem = SVFileUtils.getPathFirstElem(incfile);
		
			// Search through all the leaf directories
			for (int i=0; i<fResolvedIncDirs.size(); i++) {
				if (fIncDirDirs.get(i).contains(first_elem)) {
					String try_path = fResolvedIncDirs.get(i) + "/" + incfile;
					InputStream in = fFSProvider.openStream(try_path);
					
					if (in != null) {
						ret = new Tuple<String, InputStream>(try_path, in);
						fIncludeMap.put(incfile, fResolvedIncDirs.get(i));
						break;
					}
				}
			}
	
			if (ret == null) {
				fFailedSearches.add(incfile);
			}
		}

		/*
		for (String incdir : fIncDirs) {
			String resolved_path = SVFileUtils.resolvePath(
					incfile, incdir, fFSProvider, true);
			
			if (fFSProvider.fileExists(resolved_path)) {
				InputStream in = fFSProvider.openStream(resolved_path);
				ret = new Tuple<String, InputStream>(resolved_path, in);
				break;
			}
		}
		 */

		return ret;
	}
	
	private void buildIncludeCache() {
		fIncludeMap.clear();
		fResolvedIncDirs.clear();
		fIncDirFiles.clear();
		fIncDirDirs.clear();
		fFailedSearches.clear();
	
		for (String inc_dir : fIncDirs) {
			addIncDir(inc_dir);
		}
		
		fIncludeCacheValid = true;
	}
	
	private void addIncDir(String inc_dir) {
		String resolved_inc_dir = SVFileUtils.resolvePath(
				inc_dir, inc_dir, fFSProvider, true);
		
		Set<String> inc_dir_files = new HashSet<String>();
		Set<String> inc_dir_dirs = new HashSet<String>();
		
		// List all elements in the directory
		if (fFSProvider.isDir(resolved_inc_dir)) {
			List<String> fd_l = fFSProvider.getFiles(resolved_inc_dir);
			
			for (String fd : fd_l) {
				if (fFSProvider.isDir(fd)) {
					inc_dir_dirs.add(SVFileUtils.getPathLeaf(fd));
				} else {
					String leaf = SVFileUtils.getPathLeaf(fd);
					inc_dir_files.add(leaf);
					
					if (!fIncludeMap.containsKey(leaf)) {
						fIncludeMap.put(leaf, resolved_inc_dir);
					}
				}
			}
		}

		fResolvedIncDirs.add(resolved_inc_dir);
		fIncDirFiles.add(inc_dir_files);
		fIncDirDirs.add(inc_dir_dirs);		
	}

}
