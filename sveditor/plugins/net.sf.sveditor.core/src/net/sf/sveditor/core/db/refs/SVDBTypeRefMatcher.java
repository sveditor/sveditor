package net.sf.sveditor.core.db.refs;


public class SVDBTypeRefMatcher implements ISVDBRefMatcher {
	
	

	@Override
	public boolean matches(ISVDBRefSearchSpec ref_spec, SVDBRefItem item) {
		// TODO Auto-generated method stub
		return false;
	}

	/** MSB:
	public void find_matches(
			List<SVDBRefCacheItem>	matches,
			SVDBRefCacheEntry 		item, 
			String 					name) {
		if (item.getRefSet(SVDBRefType.TypeReference).contains(name)) {
			matches.add(new SVDBRefCacheItem(item, null, SVDBRefType.TypeReference, name));
		}
	}
	 */

}
