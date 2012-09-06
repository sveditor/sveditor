package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBAllTypeMatcher implements ISVDBFindNameMatcher {

	public boolean match(ISVDBNamedItem it, String name) {
		return it.getType().isElemOf(
				SVDBItemType.ClassDecl,
				SVDBItemType.ModuleDecl,
				SVDBItemType.InterfaceDecl);
	}

}
