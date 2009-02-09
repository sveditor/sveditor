package net.sf.sveditor.core;

import java.io.File;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;

public interface ISVDBIndex {
	int IT_IncludePath      = 1;
	int IT_BuildPath        = 2;
	int IT_IndexList        = 3;
	
	/**
	 * Cleans up this entry
	 */
	void dispose();
	
	/**
	 * Returns the base location for this index.
	 * @return
	 */
	File getBaseLocation();
	
	/**
	 * Returns the index type
	 * 
	 * @return
	 */
	int getIndexType();

	/**
	 * Returns the parsed list of files
	 * 
	 * This is a map, so that it is possible in the future to
	 * abstract away the notion of 'list'
	 * 
	 * NOTE: this method is non-functional if the index is an Include Path
	 * @return
	 */
	Map<File, SVDBFile> getFileDB();
	
	/**
	 * Returns the file tree for this index
	 * @return
	 */
	Map<File, SVDBFileTree> getFileTree();

	/**
	 * Finds the specified file within this index. Returns 'null' if
	 * it cannot be located
	 * 
	 * @param path
	 * @return
	 */
	SVDBFile findFile(File path);
	
	/**
	 * Locates a file with the following leaf. If the file cannot be
	 * found, returns 'null'
	 * 
	 * @param suffix
	 * @return
	 */
	SVDBFileTree findIncludedFile(String leaf);
	

	/**
	 * Forces a rebuild of the index
	 */
	void rebuildIndex();
	
	// TODO: add support for change listeners ???
}
