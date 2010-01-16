package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;

public interface ISVDBItemVisitor {
	
	int CONTINUE                  = 0;
	int DONT_RECURSE              = 1;
	int CANCEL                    = 2;
	
	/**
	 * Called to process the specified item
	 * 
	 * @param index The index that contains this item
	 * @param item
	 * @return
	 */
	int accept(ISVDBIndex index, SVDBItem item);

}
