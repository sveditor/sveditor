package net.sf.sveditor.core.db.refs;

import java.util.List;

public interface ISVDBRefMatcher {
	
	void find_matches(
			List<SVDBRefCacheItem>	matches,
			SVDBRefCacheEntry 		item, 
			String 					name);

}
