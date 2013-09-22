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


package net.sf.sveditor.core.tests;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class FileIndexIterator extends SVDBArgFileIndex2 {
	
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
//		loadIndex(new NullProgressMonitor());
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
		
		addFile(build_data, fFile.getFilePath(), false);
		
		cacheDeclarations(build_data, fFile, fFileTree);
		
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
