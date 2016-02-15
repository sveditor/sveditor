/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlanner;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndex extends 
	ISVDBIndexIterator, ISVDBDeclCache,
	ISVDBIndexChangePlanner, ISVDBIndexOperationRunner,
	ISVDBIndexParse {
	
	ISVDBFileSystemProvider getFileSystemProvider();
	
	void setFileSystemProvider(ISVDBFileSystemProvider fs_provider);
	
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder);

	/**
	 * Cleans up this entry
	 */
	void dispose();
	
	/**
	 * Returns the base location for this index.
	 * @return
	 */
	String getBaseLocation();
	
	String getProject();
	
	void setGlobalDefine(String key, String val);
	
	void clearGlobalDefines();
	
	/**
	 * Returns the type identifier for this index. This is
	 * typically used in conjunction with the database factory
	 */
	String getTypeID();
	
	Iterable<String> getFileList(IProgressMonitor monitor);
	
//	String getFilePath(SVDBLocation loc);
	
	List<SVDBMarker> getMarkers(String path);

	/**
	 * Finds the specified file within this index. Returns 'null' if
	 * it cannot be located
	 * 
	 * @param path
	 * @return
	 */
	SVDBFile findFile(String path);

	/**
	 * Finds the specified FileTree within this index. Returns 'null' 
	 * if it cannot be located
	 * 
	 * @param path
	 * @return
	 */
	SVDBFileTree findFileTree(String path, boolean is_argfile);
	
	/**
	 * Finds the specified file within the pre-processor index
	 * fs
	 * @param path
	 * @return
	 */
	SVDBFile findPreProcFile(String path);
	
	/**
	 * Returns whether the specified path is managed by this
	 * index
	 */
	boolean doesIndexManagePath(String path);

	/**
	 * Forces a rebuild of the index
	 */
	void rebuildIndex(IProgressMonitor monitor);
	
	/**
	 * 
	 */
	void addChangeListener(ISVDBIndexChangeListener l);
	
	void removeChangeListener(ISVDBIndexChangeListener l);
	
	// TODO: add support for change listeners ???
	
	ISVDBIndexCache getCache();
	
	void loadIndex(IProgressMonitor monitor);

	/**
	 * Quickly report whether the index is loaded and ready
	 * @return
	 */
	boolean isLoaded();
	
	/**
	 * Quickly report whether the list of files is available
	 * @return
	 */
	boolean isFileListLoaded();
	
	SVDBIndexConfig getConfig();


}
