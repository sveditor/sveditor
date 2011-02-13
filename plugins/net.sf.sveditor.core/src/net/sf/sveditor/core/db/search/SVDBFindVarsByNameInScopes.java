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

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmtType;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

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
	
	public List<ISVDBItemBase> find(
			ISVDBChildItem 	context, 
			String 			name,
			boolean			stop_on_first_match) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		ISVDBChildItem context_save = context;

		// Search up the scope
		while (context != null) {
			
			// First, search the local variables
			for (ISVDBItemBase it : context.getChildren()) {
				if (SVDBStmt.isType(it, SVDBStmtType.VarDecl)) {
					if (((SVDBVarDeclStmt)it).getName().equals(name)) {
						ret.add((SVDBVarDeclStmt)it);
						
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
				for (ISVDBNamedItem it : ((SVDBTaskFuncScope)context).getParams()) {
					if (fMatcher.match(it, name)) {
						ret.add(it);
						
						if (stop_on_first_match) {
							break;
						}
					}
				}
			} else if (context.getType() == SVDBItemType.Module) {
				SVDBModIfcClassDecl m = (SVDBModIfcClassDecl)context;
				for (SVDBParamPort p : m.getPorts()) {
					if (fMatcher.match(p, name)) {
						ret.add(p);
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
		
		// If the initial scope is in a class, then search the class
		// hierarchy
		if (ret.size() == 0 || !stop_on_first_match) {
			context = context_save;
			while (context != null && 
					!(context instanceof SVDBModIfcClassDecl)) {
				context = context.getParent();
			}
			
			if (context != null) {
				SVDBModIfcClassDecl cls = (SVDBModIfcClassDecl)context;
				
				while (cls != null) {
					for (ISVDBItemBase it : cls.getItems()) {
						if (SVDBStmt.isType(it, SVDBStmtType.VarDecl) ||
								it.getType() == SVDBItemType.Covergroup ||
								it.getType() == SVDBItemType.Coverpoint) {
							if (fMatcher.match((ISVDBNamedItem)it, name)) {
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
