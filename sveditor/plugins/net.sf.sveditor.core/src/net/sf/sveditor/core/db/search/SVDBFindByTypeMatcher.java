package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindByTypeMatcher implements ISVDBFindNameMatcher {
	private SVDBItemType			fTypes[];
	
	public SVDBFindByTypeMatcher(SVDBItemType ... types) {
		fTypes = types;
	}

	@Override
	public boolean match(ISVDBNamedItem it, String name) {
		return (fTypes == null || fTypes.length == 0 ||
				it.getType().isElemOf(fTypes));
	}
}
