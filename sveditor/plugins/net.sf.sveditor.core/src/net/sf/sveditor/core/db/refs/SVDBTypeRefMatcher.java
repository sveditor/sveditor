package net.sf.sveditor.core.db.refs;

import java.util.List;

public class SVDBTypeRefMatcher implements ISVDBRefMatcher {

	public void find_matches(
			List<SVDBRefCacheItem>	matches,
			SVDBRefCacheEntry 		item, 
			String 					name) {
		if (item.getRefSet(SVDBRefType.TypeReference).contains(name)) {
			matches.add(new SVDBRefCacheItem(item, null, SVDBRefType.TypeReference, name));
		}
	}

}
