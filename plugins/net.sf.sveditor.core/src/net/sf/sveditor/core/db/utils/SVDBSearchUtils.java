package net.sf.sveditor.core.db.utils;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBSearchUtils {
	
	public static List<SVDBItem> findItemsByType(
			SVDBScopeItem			scope,
			SVDBItemType	...		types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : scope.getItems()) {
			boolean match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					match = true;
					break;
				}
			}
			
			if (match) {
				ret.add(it);
			}
		}
		
		return ret;
	}

	public static List<SVDBItem> findItemsByName(
			SVDBScopeItem			scope,
			String					name,
			SVDBItemType	...		types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : scope.getItems()) {
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
