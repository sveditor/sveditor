package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBFindByName {
	private ISVDBIndexIterator			fIndexIterator;
	
	public SVDBFindByName(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
	}
	
	public List<SVDBItem> find(String name, SVDBItemType ... types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		ISVDBItemIterator<SVDBItem> item_it = fIndexIterator.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			boolean type_match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					type_match = true;
					break;
				}
			}
			
			if (type_match && it.getName() != null && it.getName().equals(name)) {
				ret.add(it);
			}
		}
		
		return ret;
	}

}
