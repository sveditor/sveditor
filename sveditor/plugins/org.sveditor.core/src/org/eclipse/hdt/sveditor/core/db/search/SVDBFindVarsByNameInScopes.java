/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;

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
		while (context != null && context instanceof ISVDBChildParent) {
			
			// First, search the local variables
			for (ISVDBItemBase it : ((ISVDBChildParent)context).getChildren()) {
				if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
					boolean stop = false;
					for (ISVDBChildItem c : ((SVDBVarDeclStmt)it).getChildren()) {
						SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
						if (vi.getName().equals(name)) {
							ret.add(vi);
							
							if (stop_on_first_match) {
								stop = true;
								break;
							}
						}
						if (stop) {
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
				for (SVDBParamPortDecl it : ((SVDBTask)context).getParams()) {
					boolean stop = false;
					for (ISVDBChildItem c : it.getChildren()) {
						SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
						if (fMatcher.match(vi, name)) {
							ret.add(vi);
							
							if (stop_on_first_match) {
								stop = true;
								break;
							}
						}
					}
					if (stop) {
						break;
					}
				}
			} else if (context.getType() == SVDBItemType.ModuleDecl) {
				SVDBModIfcDecl m = (SVDBModIfcDecl)context;
				for (SVDBParamPortDecl p : m.getPorts()) {
					boolean stop = false;
					for (ISVDBChildItem c : p.getChildren()) {
						SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
						if (fMatcher.match(vi, name)) {
							ret.add(vi);
							if (stop_on_first_match) {
								stop = true;
								break;
							}
						}
					}
					if (stop) {
						break;
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
			while (context != null && context.getType() != SVDBItemType.ClassDecl) {
				context = context.getParent();
			}
			
			if (context != null) {
				SVDBClassDecl cls = (SVDBClassDecl)context;
				
				while (cls != null) {
					for (ISVDBItemBase it : cls.getChildren()) {
						if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt) ||
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
