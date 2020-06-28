/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexCache {
	
	enum FileType {
		Invalid,
		ArgFile,
		SVFile
	}
	
	ISVDBIndexCacheMgr getCacheMgr();
	
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
	boolean init(IProgressMonitor monitor, Object index_data, String base_location);
	
	/**
	 * Invalidate this cache, clearing any backing storage
	 */
	void clear(IProgressMonitor monitor);
	
	/**
	 * Return a list of the file paths present in this
	 * index. This is a non-time-consuming operation
	 * 
	 * @return
	 */
	Set<String> getFileList(boolean is_argfile);
	
	long getLastModified(String path);
	
	void setLastModified(String path, long timestamp, boolean is_argfile);
	
	void addFile(String path, boolean is_argfile);
	
	List<SVDBMarker> getMarkers(String path);
	
	void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile);
	
	/**
	 * Returns the pre-processor view of the file
	 */
	SVDBFile getPreProcFile(IProgressMonitor monitor, String path);
	
	void setPreProcFile(String path, SVDBFile file);
	
	/**
	 * Returns the file tree for the specified file
	 */
	SVDBFileTree getFileTree(IProgressMonitor monitor, String path, boolean is_argfile);
	
	void setFileTree(String path, SVDBFileTree file, boolean is_argfile);
	
	/**
	 * Returns the full-parse view of the file
	 */
	SVDBFile getFile(IProgressMonitor monitor, String path);
	
	void setFile(String path, SVDBFile file, boolean is_argfile);
	
	void removeFile(String path, boolean is_argfile);
	
	/**
	 * 
	 */
	Map<Integer, SVDBFile> getSubFileMap(String path);
	
	void setSubFileMap(String path, Map<Integer, SVDBFile> map);
		
	
	/**
	 * Returns the type of the given file
	 */
	FileType getFileType(String path);
	
	/**
	 * Synchronize the cache with the backing storage
	 */
	void sync();

	/**
	 * Cleans up after this cache. 
	 */
	void dispose();

}
