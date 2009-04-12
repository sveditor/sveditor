package net.sf.sveditor.core.db.index;

import java.io.File;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBIndex {
	int IT_IncludePath      = 1;
	int IT_BuildPath        = 2;
	int IT_IndexList        = 3;
	
	void init(ISVDBIndexRegistry registry);
	
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
	 * Returns the type identifier for this index. This is
	 * typically used in conjunction with the database factory
	 */
	String getTypeID();
	
	/**
	 * Returns whether this database has loaded information from all its files
	 */
	boolean isLoaded();
	
	/**
	 * Load this index from the specified lists
	 */
	void load(List<SVDBFile> pp_files, List<SVDBFile> db_files);
	
	/**
	 * Sets the containing index. This is typically used to pass the 
	 * project's index to a client so that include files from some external
	 * library can be located by a sub-index
	 * @param index
	 */
	void setSuperIndex(ISVDBIndex index);
	
	ISVDBIndex getSuperIndex();
	
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
	 * Returns list of SVDBFile with pre-proc info
	 * 
	 * @return
	 */
	Map<File, SVDBFile> getPreProcFileMap();

	/**
	 * Finds the specified file within this index. Returns 'null' if
	 * it cannot be located
	 * 
	 * @param path
	 * @return
	 */
	SVDBFile findFile(File path);
	
	/**
	 * Finds the specified file within the pre-processor index
	 * fs
	 * @param path
	 * @return
	 */
	SVDBFile findPreProcFile(File path);
	
	/**
	 * Locates a file with the following leaf. If the file cannot be
	 * found, returns 'null'
	 * 
	 * @param suffix
	 * @return
	 */
	SVDBFile findIncludedFile(String leaf);
	

	/**
	 * Forces a rebuild of the index
	 */
	void rebuildIndex();
	
	/**
	 * 
	 */
	void addChangeListener(ISVDBIndexChangeListener l);
	
	void removeChangeListener(ISVDBIndexChangeListener l);
	
	// TODO: add support for change listeners ???
}
