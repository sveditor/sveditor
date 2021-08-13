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
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVDBFindByNameInClassHierarchy {
	private ISVDBIndexIterator				fIndexIterator;
	private LogHandle						fLog;
	private ISVDBFindNameMatcher			fMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	protected List<ISVDBItemBase>			fRet;
	
	
	public SVDBFindByNameInClassHierarchy(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
		fLog = LogFactory.getLogHandle("FindByNameInClassHierarchy");
	}
	
	protected void add(ISVDBItemBase item, int scope_level) {
		fRet.add(item);
	}
	
	public List<ISVDBItemBase> find(
			ISVDBChildItem 		scope, 
			String 				id,
			SVDBItemType	...	types) {
		return find(scope, id, false, false, types);
	}
	
	public List<ISVDBItemBase> find(
			ISVDBChildItem 		scope, 
			String 				id,
			boolean				exclude_nonstatic,
			boolean				exclude_static,
			SVDBItemType	...	types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		int scope_level = 0;
		
		fRet = ret;
		
		fLog.debug("--> find(" + ((scope != null)?SVDBItem.getName(scope):null) + " \"" + id + "\")");
		for (SVDBItemType t : types) {
			fLog.debug("    TYPE " + t);
		}
		
		if (scope != null && 
				SVDBScopeItem.getName(scope) != null && 
				SVDBScopeItem.getName(scope).indexOf("::") != -1) {
			// Looks like an extern function
			String clsname = ((ISVDBNamedItem)scope).getName().substring(0, 
					((ISVDBNamedItem)scope).getName().indexOf("::"));
		
			SVDBFindNamedModIfcClassIfc finder = new SVDBFindNamedModIfcClassIfc(fIndexIterator);
			List<SVDBDeclCacheItem> result = finder.findItems(clsname);
			
			if (result.size() > 0) {
				scope = (ISVDBChildItem)result.get(0).getSVDBItem();
			}
		} else {
			// Assume we're in a containing scope
			while (scope != null && 
					scope.getType() != SVDBItemType.ClassDecl &&
					scope.getType() != SVDBItemType.InterfaceDecl &&
					scope.getType() != SVDBItemType.ModuleDecl &&
					scope.getType() != SVDBItemType.Covergroup &&
					scope.getType() != SVDBItemType.Coverpoint) {
				fLog.debug("Searching up-scope (current is " + scope.getType() + 
						" " + SVDBItem.getName(scope) + ")");
				if (scope.getType() == SVDBItemType.Task || scope.getType() == SVDBItemType.Function) {
					findTFParamsLocals(ret, (SVDBTask)scope, id, types);
				}
				scope = scope.getParent();
			}
		}
		
		if (scope == null) {
			fLog.debug("Failed to find Class/Struct scope");
			fLog.debug("<-- find(\"" + id + "\") returns " + ret.size() + " results");
			return ret;
		}
		
		// Now, search through the scope and the class hierarchy
		while (scope != null && scope instanceof ISVDBChildParent) {
			fLog.debug("Searching scope \"" + ((ISVDBNamedItem)scope).getName() + "\"");
			for (ISVDBItemBase it : ((ISVDBChildParent)scope).getChildren()) {
				boolean matches = (types.length == 0);
				
				for (SVDBItemType type : types) {
					if (it.getType() == type) {
						matches = true;
						break;
					}
				}

				if (matches) {
					if (it.getType() == SVDBItemType.VarDeclStmt) {
						SVDBVarDeclStmt var = (SVDBVarDeclStmt)it;
						boolean is_static = (var.getAttr() & SVDBVarDeclStmt.FieldAttr_Static) != 0;
					
						if ((is_static && !exclude_static) || (!is_static && !exclude_nonstatic)) {
							for (ISVDBChildItem it_t : ((SVDBVarDeclStmt)it).getChildren()) {
								if (fMatcher.match((ISVDBNamedItem)it_t, id)) {
									add(it_t, scope_level);
								}
							}
						}
					} else if (it instanceof ISVDBNamedItem) {
						if (fMatcher.match((ISVDBNamedItem)it, id)) {
							add(it, scope_level);
						}
					}
				}
			}

			// Always match exact
			if (scope instanceof SVDBClassDecl) {
				SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIterator, fDefaultMatcher);
				if (((SVDBClassDecl)scope).getSuperClass() != null) {
					String super_name = ((SVDBClassDecl)scope).getSuperClass().getName();
					fLog.debug("Searching for super-class \"" +  super_name + "\""); 
					scope = finder.find((SVDBClassDecl)scope);
					if (scope != null) {
						fLog.debug("Find super-class \"" + 
								((SVDBClassDecl)scope).getSuperClass() + "\" returns " + scope);
					} else {
						fLog.debug("Failed to find super-class \"" +  super_name + "\""); 
					}
				} else {
					fLog.debug("No super-class");
					scope = null;
				}
			} else {
				scope = null;
			}
			scope_level++;
		}
		
		fLog.debug("<-- find(\"" + id + "\") returns " + ret.size() + " results");
		return ret;
	}
	
	private void findTFParamsLocals(
			List<ISVDBItemBase>	items,
			SVDBTask 	scope, 
			String 				id,
			SVDBItemType	...	types) {
		boolean matches = (types.length == 0);

		for (SVDBParamPortDecl it : scope.getParams()) {
			for (SVDBItemType type : types) {
				if (it.getType() == type) {
					matches = true;
					break;
				}
			}
			
			if (matches) {
				for (ISVDBChildItem c : it.getChildren()) {
					SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
					if (fMatcher.match(vi, id)) {
						items.add(vi);
					}
				}
			}
		}
		
		for (ISVDBItemBase it : scope.getChildren()) {
			for (SVDBItemType type : types) {
				if (it.getType() == type) {
					matches = true;
					break;
				}
			}
			
			if (matches && it instanceof ISVDBNamedItem) {
				if (fMatcher.match((ISVDBNamedItem)it, id)) {
					items.add(it);
				}
			}
		}
	}
}
