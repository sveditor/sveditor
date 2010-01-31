package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;

public class SVDBFindDefaultNameMatcher implements ISVDBFindNameMatcher {
	
	static SVDBFindDefaultNameMatcher 		fDefault;

	public boolean match(SVDBItem it, String name) {
		return (it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindDefaultNameMatcher();
		}
		return fDefault;
	}
	
}
