package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBFindNamedModIfcClassIfc {
	ISVDBIndexIterator			fIndexIt;
	
	public SVDBFindNamedModIfcClassIfc(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}
	
	public SVDBModIfcClassDecl find(String type_name) {
		ISVDBItemIterator<SVDBItem> item_it = fIndexIt.getItemIterator();
		SVDBModIfcClassDecl ret = null;
		
		while (item_it.hasNext()) {
			boolean had_next = item_it.hasNext();
			SVDBItem it = item_it.nextItem();
			
			if (it == null) {
				System.out.println("it == null ; hasNext=" + had_next);
			}
			
			if ((it.getType() == SVDBItemType.Class ||
					it.getType() == SVDBItemType.Module ||
					it.getType() == SVDBItemType.Interface) && 
				it.getName().equals(type_name)) {
				ret = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		return ret;
	}

}
