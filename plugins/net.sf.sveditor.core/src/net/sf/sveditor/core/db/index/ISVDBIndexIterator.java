package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

public interface ISVDBIndexIterator {
	
	ISVDBItemIterator<SVDBItem> 		getItemIterator();
	
}
