/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindByNameInScopes {
	
	public SVDBFindByNameInScopes(ISVDBIndexIterator index_it) {
	}
	
	public List<SVDBItem> find(
			SVDBScopeItem			context,
			String					name,
			boolean					stop_on_first_match,
			SVDBItemType	...		types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();


		// Search up the scope
		while (context != null) {
			
			// First, search the local variables
			for (SVDBItem it : context.getItems()) {
				if (it.getName().equals(name)) {
					boolean match = (types.length == 0);

					for (SVDBItemType t : types) {
						if (it.getType() == t) {
							match = true;
							break;
						}
					}
					
					if (match) {
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
					System.out.println("check param \"" + it.getName() + "\"");
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
