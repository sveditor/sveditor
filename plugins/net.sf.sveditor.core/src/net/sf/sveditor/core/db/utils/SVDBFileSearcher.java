package net.sf.sveditor.core.db.utils;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBVarDeclItem;

public class SVDBFileSearcher {
	private SVDBFile			fFile;
	
	public SVDBFileSearcher(SVDBFile file) {
		fFile = file;
	}
	
	public SVDBScopeItem findActiveScope(int lineno) {
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
