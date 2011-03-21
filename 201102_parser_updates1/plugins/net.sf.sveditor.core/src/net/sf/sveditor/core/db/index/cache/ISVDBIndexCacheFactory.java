package net.sf.sveditor.core.db.index.cache;

public interface ISVDBIndexCacheFactory {
	
	ISVDBIndexCache createIndexCache(String project_name, String base_location);

	// TODO: require a mechanism to clean up unneeded cache

}
