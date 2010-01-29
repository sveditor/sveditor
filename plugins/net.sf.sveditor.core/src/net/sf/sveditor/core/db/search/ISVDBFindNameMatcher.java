package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;

public interface ISVDBFindNameMatcher {
	
	boolean match(SVDBItem it, String name);

}
