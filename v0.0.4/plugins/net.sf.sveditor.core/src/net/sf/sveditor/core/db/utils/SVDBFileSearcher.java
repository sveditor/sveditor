package net.sf.sveditor.core.db.utils;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBFileSearcher {
	private SVDBFile			fFile;
	
	public SVDBFileSearcher(SVDBFile file) {
		fFile = file;
	}
	
	public SVDBScopeItem findActiveScope(int lineno) {
		return findActiveScope(fFile, lineno);
		/*
		SVDBScopeItem item = null;
		
		for (int i=0; i<fFile.getItems().size(); i++) {
			SVDBItem it_1 = fFile.getItems().get(i);
			SVDBItem it_2 = (i+1<fFile.getItems().size())?
					fFile.getItems().get(i+1):null;
					
			if (it_1 instanceof SVDBScopeItem) {
				SVDBScopeItem s_it = (SVDBScopeItem)it_1;
				if (lineno >= s_it.getLocation().getLine() &&
					(it_2 == null || lineno <= it_2.getLocation().getLine())) {
					SVDBScopeItem tmp = refineSearch(s_it, lineno);
					
					if (tmp != null) {
						item = tmp;
					} else {
						item = s_it;
					}
				}
			}
		}
		
		return item;
		 */
	}
	
	private SVDBScopeItem findActiveScope(SVDBScopeItem p, int lineno) {
		for (SVDBItem it : p.getItems()) {
			if (it instanceof SVDBScopeItem) {
				SVDBScopeItem s_it = (SVDBScopeItem)it;
				if (s_it.getLocation() != null && s_it.getEndLocation() != null) {
					if (lineno >= s_it.getLocation().getLine() && 
							lineno <= s_it.getEndLocation().getLine()) {
						SVDBScopeItem s_it_p = findActiveScope(s_it, lineno);
						
						if (s_it_p != null) {
							return s_it_p;
						} else {
							return s_it;
						}
					}
				}
			}
		}
		
		return null;
	}
	
	private SVDBScopeItem refineSearch(SVDBScopeItem p, int lineno) {
		SVDBScopeItem ret = null;
		
		for (int i=0; i<p.getItems().size(); i++) {
			SVDBItem it_1 = p.getItems().get(i);
			SVDBItem it_2 = (i+1<p.getItems().size())?
					p.getItems().get(i+1):null;
			if (it_1 instanceof SVDBScopeItem) {
				SVDBScopeItem s_it = (SVDBScopeItem)it_1;
				if (lineno >= s_it.getLocation().getLine() &&
						(it_2 == null || lineno <= it_2.getLocation().getLine())) {
					SVDBScopeItem ret_t = refineSearch(s_it, lineno);
					
					if (ret_t != null) {
						ret = ret_t;
					} else {
						ret = s_it; 
					}
				}
			}
		}
		
		return ret;
	}

}
