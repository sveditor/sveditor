package net.sf.sveditor.core.db.index.cache;

import java.util.List;

public interface ISVDBIndexCacheFactory {
	
	ISVDBIndexCache createIndexCache(String project_name, String base_location);
	
	/**
	 * Must compact the cache storage by removing elements not in the 
	 * cache_list
	 * 
	 * @param cache_list
	 */
	void compactCache(List<ISVDBIndexCache> cache_list);

	// TODO: require a mechanism to clean up unneeded cache

}
