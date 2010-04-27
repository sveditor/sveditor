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
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindVarsByNameInScopes {
	
	private ISVDBIndexIterator				fIndexIterator;
	private ISVDBFindNameMatcher			fMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	
	public SVDBFindVarsByNameInScopes(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
	}
	
	public List<SVDBItem> find(
			SVDBScopeItem 	context, 
			String 			name,
			boolean			stop_on_first_match) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		SVDBScopeItem context_save = context;

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
					if (fMatcher.match(it, name)) {
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
		
		if (ret.size() == 0 || !stop_on_first_match) {
			context = context_save;
			while (context != null && 
					!(context instanceof SVDBModIfcClassDecl)) {
				context = context.getParent();
			}
			
			if (context != null) {
				SVDBModIfcClassDecl cls = (SVDBModIfcClassDecl)context;
				
				while (cls != null) {
					for (SVDBItem it : cls.getItems()) {
						if (it.getType() == SVDBItemType.VarDecl ||
								it.getType() == SVDBItemType.Covergroup ||
								it.getType() == SVDBItemType.Coverpoint) {
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
					
					SVDBFindSuperClass finder = 
						new SVDBFindSuperClass(fIndexIterator, fDefaultMatcher);
					cls = finder.find(cls);
				}
			}
		}
		
		return ret;
	}

}
