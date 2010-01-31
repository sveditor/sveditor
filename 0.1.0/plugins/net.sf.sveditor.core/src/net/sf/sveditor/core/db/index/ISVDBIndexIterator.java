package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBItem;

public interface ISVDBIndexIterator {
	
	ISVDBItemIterator<SVDBItem> 		getItemIterator();
	
}
