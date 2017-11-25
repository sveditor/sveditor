package net.sf.sveditor.core.db.index.cache;

import java.util.List;

public class InMemoryIndexCacheMgr implements ISVDBIndexCacheMgr {

	@Override
	public ISVDBIndexCache findIndexCache(String project_name, String base_location) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
		return new InMemoryIndexCache(this);
	}

	@Override
	public void compactCache(List<ISVDBIndexCache> cache_list) { }

	@Override
	public void dispose() { }

	@Override
	public void sync() { }

}
