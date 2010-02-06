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

import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public interface ISVDBIndex extends ISVDBFileFactory, ISVDBIndexIterator, ISVDBIncludeFileProvider {
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
	String getBaseLocation();
	
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
	 * Dump index-specific data
	 */
	void dump(IDBWriter			index_data);
	
	/**
	 * Load this index from the specified lists
	 */
	void load(
			IDBReader			index_data,
			List<SVDBFile> 		pp_files, 
			List<SVDBFile> 		db_files) throws DBFormatException;
	
	/**
	 * Sets the include provider
	 * 
	 * @param index
	 */
	void setIncludeFileProvider(ISVDBIncludeFileProvider inc_provider);
	
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
	Map<String, SVDBFile> getFileDB();
	
	/**
	 * Returns list of SVDBFile with pre-proc info
	 * 
	 * @return
	 */
	Map<String, SVDBFile> getPreProcFileMap();

	/**
	 * Finds the specified file within this index. Returns 'null' if
	 * it cannot be located
	 * 
	 * @param path
	 * @return
	 */
	SVDBFile findFile(String path);
	
	/**
	 * Finds the specified file within the pre-processor index
	 * fs
	 * @param path
	 * @return
	 */
	SVDBFile findPreProcFile(String path);
	
	

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
