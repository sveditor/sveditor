package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

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
	
	public List<SVDBModIfcClassDecl> find(String type_name, boolean match_prefix) {
		ISVDBItemIterator<SVDBItem> item_it = fIndexIt.getItemIterator();
		List<SVDBModIfcClassDecl> ret = new ArrayList<SVDBModIfcClassDecl>();
		
		while (item_it.hasNext()) {
			boolean had_next = item_it.hasNext();
			SVDBItem it = item_it.nextItem();
			
			if (it == null) {
				System.out.println("it == null ; hasNext=" + had_next);
			}
			
			if ((it.getType() == SVDBItemType.Class ||
					it.getType() == SVDBItemType.Module ||
					it.getType() == SVDBItemType.Interface ||
					it.getType() == SVDBItemType.Struct)) {
				if (match_prefix) {
					if (type_name.equals("") || it.getName().startsWith(type_name)) {
						ret.add((SVDBModIfcClassDecl)it);
					}
				} else {
					if (it.getName().equals(type_name)) {
						ret.add((SVDBModIfcClassDecl)it);
					}
				}
			}
		}
		
		return ret;
	}

}
