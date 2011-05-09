package net.sf.sveditor.core.tests;

import java.util.List;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;

public class TestNullIndexCacheFactory implements ISVDBIndexCacheFactory {

	public ISVDBIndexCache createIndexCache(String project_name,
			String base_location) {
		return new TestNullIndexCache();
	}

	public void compactCache(List<ISVDBIndexCache> cache_list) {
	}

}
