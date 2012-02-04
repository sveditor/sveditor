package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindClassDefaultNameMatcher implements ISVDBFindNameMatcher {

	static SVDBFindClassDefaultNameMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return (it.getType() == SVDBItemType.ClassDecl &&
				it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindClassDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindClassDefaultNameMatcher();
		}
		return fDefault;
	}

}
