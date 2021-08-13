/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.tests;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBFileTree;
import org.sveditor.core.db.index.SVDBFSFileSystemProvider;
import org.sveditor.core.db.index.argfile.SVDBArgFileBuildDataUtils;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;

public class FileIndexIterator extends SVDBArgFileIndex {
	
	private SVDBFile				fFile;
	private SVDBFileTree			fFileTree;
	private SVDBFile				fPPFile;
	Map<String, SVDBFile>			fFileMap;
	
	public static ISVDBIndexCache createCache(ISVDBIndexCacheMgr cache_factory) {
		return cache_factory.createIndexCache("project", "base");
	}
	
	public FileIndexIterator(SVDBFile file, ISVDBIndexCache cache) {
		super("project", "base", new SVDBFSFileSystemProvider(), cache, null);
		fFile = file;
		fFileTree = new SVDBFileTree(fFile.getFilePath());
		fFileMap = new HashMap<String, SVDBFile>();
		
		fFileMap.put(file.getName(), file);
		init(new NullProgressMonitor(), null);
		rebuild_index(new NullProgressMonitor());
	}
	
	public FileIndexIterator(
			Tuple<SVDBFile, SVDBFile> 	file,
			ISVDBIndexCache				cache) {
		super("project", "base", new SVDBFSFileSystemProvider(), cache, null);
		fPPFile = file.first();
		fFile = file.second();
		fFileMap = new HashMap<String, SVDBFile>();
		
		fFileMap.put(fFile.getName(), fFile);
		init(new NullProgressMonitor(), null);
		loadIndex(new NullProgressMonitor());
	}
	
	public String getTypeID() {
		return "FileIndexIterator";
	}
	
	@Override
	protected void buildIndex(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData 	build_data) {
		
		build_data.addFile(fFile.getFilePath(), false);
		
		SVDBArgFileBuildDataUtils.cacheDeclarations(
				build_data, this, fFile, fFileTree);
		
		build_data.getCache().setFile(fFile.getFilePath(), fFile, false);
	}

	/*
	protected SVDBFile processPreProcFile(String path) {
		// Do Nothing
		cacheDeclarations(fFile);
		cacheReferences(fFile);
		getCache().setFile(fFile.getFilePath(), fFile, false);
		return null;
	}
	 */
	
	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFile;
		} else {
			return super.findFile(monitor, path);
		}
	}
	
	@Override
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		if (fPPFile != null && fPPFile.getFilePath().equals(path)) {
			return fPPFile;
		} else {
			return super.findPreProcFile(monitor, path);
		}
	}

	@Override
	public synchronized SVDBFileTree findFileTree(String path, boolean is_argfile) {
		// TODO:
		return null;
	}

}
