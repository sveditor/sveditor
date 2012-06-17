package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindPackageDefaultNameMatcher implements ISVDBFindNameMatcher {

	static SVDBFindPackageDefaultNameMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return (it.getType() == SVDBItemType.PackageDecl &&
				it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindPackageDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindPackageDefaultNameMatcher();
		}
		return fDefault;
	}

}
