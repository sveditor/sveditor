package net.sf.sveditor.core.db.index.cache;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.SVDBFileTree;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexCache {
	
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
	void init(IProgressMonitor monitor, Object index_data);
	
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
	List<String> getFileList();
	
	long getLastModified(String path);
	
	void setLastModified(String path, long timestamp);
	
	void addFile(String path);
	
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
