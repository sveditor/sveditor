package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindVarsByNameInScopes {
	
	ISVDBIndexIterator				fIndexIterator;
	
	public SVDBFindVarsByNameInScopes(ISVDBIndexIterator index_it) {
		fIndexIterator = index_it;
	}
	
	public List<SVDBItem> find(
			SVDBScopeItem 	context, 
			String 			name,
			boolean			stop_on_first_match) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();

		// Search up the scope
		while (context != null) {
			
			// First, search the local variables
			for (SVDBItem it : context.getItems()) {
				if (it.getType() == SVDBItemType.VarDecl) {
					if (it.getName().equals(name)) {
						ret.add(it);
						
						if (stop_on_first_match) {
							break;
						}
					}
				}
			}
			
			if (ret.size() > 0 && stop_on_first_match) {
				break;
			}
			
			// Next, search the parameters, if we're in a function/task scope
			if (context.getType() == SVDBItemType.Function || 
					context.getType() == SVDBItemType.Task) {
				for (SVDBItem it : ((SVDBTaskFuncScope)context).getParams()) {
					if (it.getName().equals(name)) {
						ret.add(it);
						
						if (stop_on_first_match) {
							break;
						}
					}
				}
			}

			if (ret.size() > 0 && stop_on_first_match) {
				break;
			}

			context = context.getParent();
		}
		
		return ret;
	}

}
