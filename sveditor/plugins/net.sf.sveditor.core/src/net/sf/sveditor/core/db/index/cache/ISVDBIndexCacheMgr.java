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

import java.util.List;

/**
 * Interface for implementations of a cache manager. A cache 
 * manager is responsible for managing the storage and key
 * operations of a collection of index caches
 * @author ballance
 *
 */
public interface ISVDBIndexCacheMgr {

	/**
	 * Finds an existing cache by its project name and root location
	 * 
	 * @param project_name
	 * @param base_location
	 * @return
	 */
	ISVDBIndexCache findIndexCache(String project_name, String base_location);

	/**
	 * Creates a new index cache
	 * 
	 * @param project_name
	 * @param base_location
	 * @return
	 */
	ISVDBIndexCache createIndexCache(String project_name, String base_location);
	
	/**
	 * Must compact the cache storage by removing elements not in the 
	 * cache_list
	 * 
	 * @param cache_list
	 */
	void compactCache(List<ISVDBIndexCache> cache_list);

	// TODO: require a mechanism to clean up unneeded cache

	/**
	 * Shuts down the index cache manager
	 */
	void dispose();

	/**
	 * Ensures the storage of the managed index caches are synchronized
	 * with the backing mechanism
	 */
	void sync();
	
}
