package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindByNameInClassHierarchy {
	ISVDBIndexIterator		fIndexIterator;
	
	public SVDBFindByNameInClassHierarchy(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
	}
	
	public List<SVDBItem> find(
			SVDBScopeItem 		scope, 
			String 				id,
			SVDBItemType	...	types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		while (scope != null && scope.getType() != SVDBItemType.Class) {
			scope = scope.getParent();
		}
		
		if (scope == null) {
			return ret;
		}
		
		// Now, search through the scope and the class hierarchy
		while (scope != null) {
			for (SVDBItem it : scope.getItems()) {
				boolean matches = (types.length == 0);
				
				for (SVDBItemType type : types) {
					if (it.getType() == type) {
						matches = true;
						break;
					}
				}
				
				if (matches && it.getName().equals(id)) {
					ret.add(it);
				}
			}
			
			SVDBFindNamedModIfcClassIfc finder = 
				new SVDBFindNamedModIfcClassIfc(fIndexIterator);
			scope = finder.find(((SVDBModIfcClassDecl)scope).getSuperClass());
		}
		
		return ret;
	}

}
