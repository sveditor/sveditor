package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBScopeItem;

public interface ISVDBFileContextIndexSearcher extends ISVDBIndexSearcher {

	SVDBScopeItem findActiveScope(int lineno);
}
