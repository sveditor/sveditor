package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBFileContextIndexSearcher extends SVDBIndexSearcher  
		implements ISVDBFileContextIndexSearcher {
	private SVDBFile							fFileContext;
	
	public SVDBFileContextIndexSearcher(SVDBFile file) {
		fFileContext     = file;
	}
	
	public SVDBScopeItem findActiveScope(int lineno) {
		return findActiveScope(fFileContext, lineno);
	}

	/**
	 * findActiveScope()
	 * 
	 * Helper method for the public findActiveScope()
	 * @param scope
	 * @param lineno
	 * @return
	 */
	private SVDBScopeItem findActiveScope(SVDBScopeItem scope, int lineno) {
		debug("findActiveScope: " + scope.getName() + " " + lineno);
		for (SVDBItem it : scope.getItems()) {
			if (it instanceof SVDBScopeItem) {
				debug("    sub-scope " + it.getName() + " @ " + 
						it.getLocation().getLine() + "-" + 
						((SVDBScopeItem)it).getEndLocation().getLine());
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
	
}
