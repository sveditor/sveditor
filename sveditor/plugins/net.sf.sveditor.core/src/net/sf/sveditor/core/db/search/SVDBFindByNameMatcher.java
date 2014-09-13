package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindByNameMatcher implements ISVDBFindNameMatcher {
	private SVDBItemType						fTypes[];
	private static SVDBFindByNameMatcher		fDefault = null;
	
	public SVDBFindByNameMatcher(SVDBItemType ... types) {
		fTypes = types;
	}

	public boolean match(ISVDBNamedItem it, String name) {
		if (fTypes.length == 0) {
			return (it.getName().equals(name));
		} else {
			return (it.getType().isElemOf(fTypes) && it.getName().equals(name));
		}
	}
	
	public static SVDBFindByNameMatcher getDefault() { 
		if (fDefault == null) {
			fDefault = new SVDBFindByNameMatcher();
		}
		return fDefault;
	}

}
