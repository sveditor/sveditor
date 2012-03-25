/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBFileTree;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexCache {
	
	long numFilesRead();
	
	/**
	 * The cache must remove the path corresponding to this cache
	 * instance from the supplied list. This method is used in the
	 * database-compacting process 
	 */
	void removeStoragePath(List<File> db_path_list);
	
	/**
	 * Index data is data specific to the index style. This 
	 * data may include timestamps for non-SystemVerilog files, etc.
	 * Index data is persisted within the index cache. 
	 *  
	 * @param data
	 */
	void setIndexData(Object data);
	
	/**
	 * Index data is data specific to the index style. This 
	 * data may include timestamps for non-SystemVerilog files, etc.
	 * Index data is persisted within the index cache. 
	 * 
	 * @return
	 */
	Object getIndexData();

	/**
	 * Initialize the cache. This may involve reading the 
	 * index of the index 
	 * 
	 * @param monitor
	 */
	boolean init(IProgressMonitor monitor, Object index_data);
	
	/**
	 * Perform the initial load
	 */
	void initLoad(IProgressMonitor monitor);
	
	/**
	 * Invalidate this cache, clearing any backing storage
	 */
	void clear();
	
	/**
	 * Return a list of the file paths present in this
	 * index. This is a non-time-consuming operation
	 * 
	 * @return
	 */
	Set<String> getFileList();
	
	long getLastModified(String path);
	
	void setLastModified(String path, long timestamp);
	
	void addFile(String path);
	
	List<SVDBMarker> getMarkers(String path);
	
	void setMarkers(String path, List<SVDBMarker> markers);
	
	/**
	 * Returns the pre-processor view of the file
	 */
	SVDBFile getPreProcFile(IProgressMonitor monitor, String path);
	
	void setPreProcFile(String path, SVDBFile file);
	
	/**
	 * Returns the file tree for the specified file
	 */
	SVDBFileTree getFileTree(IProgressMonitor monitor, String path);
	
	void setFileTree(String path, SVDBFileTree file);
	
	/**
	 * Returns the full-parse view of the file
	 */
	SVDBFile getFile(IProgressMonitor monitor, String path);
	
	void setFile(String path, SVDBFile file);
	
	void removeFile(String path);
	
	/**
	 * Synchronize the cache with the backing storage
	 */
	void sync();
	

}
