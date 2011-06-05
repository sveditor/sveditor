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

import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndex extends ISVDBIndexIterator, ISVDBIncludeFileProvider {
	
	public void init(IProgressMonitor monitor);

	
	SVDBFile parse(
			IProgressMonitor monitor,
			InputStream in, 
			String path, 
			List<SVDBMarker> markers);
	
	/**
	 * Cleans up this entry
	 */
	void dispose();
	
	/**
	 * Returns the base location for this index.
	 * @return
	 */
	String getBaseLocation();
	
	void setGlobalDefine(String key, String val);
	
	void clearGlobalDefines();
	
	/**
	 * Returns the type identifier for this index. This is
	 * typically used in conjunction with the database factory
	 */
	String getTypeID();
	
	/**
	 * Sets the include provider
	 * 
	 * @param index
	 */
	void setIncludeFileProvider(ISVDBIncludeFileProvider inc_provider);
	
	List<String> getFileList(IProgressMonitor monitor);
	
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
	
	ISVDBIndexCache getCache();
	
	void loadIndex(IProgressMonitor monitor);
}
