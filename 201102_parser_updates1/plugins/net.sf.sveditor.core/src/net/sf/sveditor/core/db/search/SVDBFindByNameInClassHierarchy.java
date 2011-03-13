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
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFindByNameInClassHierarchy {
	private ISVDBIndexIterator				fIndexIterator;
	private LogHandle						fLog;
	private ISVDBFindNameMatcher			fMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	
	
	public SVDBFindByNameInClassHierarchy(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
		fLog = LogFactory.getLogHandle("FindByNameInClassHierarchy");
	}
	
	public List<ISVDBItemBase> find(
			ISVDBChildItem 		scope, 
			String 				id,
			SVDBItemType	...	types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		fLog.debug("--> find(" + ((scope != null)?
				((ISVDBNamedItem)scope).getName():null) + " \"" + id + "\")");
		for (SVDBItemType t : types) {
			fLog.debug("    TYPE " + t);
		}
		
		if (scope != null && 
				((ISVDBNamedItem)scope).getName() != null && 
				((ISVDBNamedItem)scope).getName().indexOf("::") != -1) {
			// Looks like an extern function
			String clsname = ((ISVDBNamedItem)scope).getName().substring(0, 
					((ISVDBNamedItem)scope).getName().indexOf("::"));
			
			SVDBFindNamedModIfcClassIfc finder = new SVDBFindNamedModIfcClassIfc(fIndexIterator);
			List<ISVDBChildItem> result = finder.find(clsname);
			
			if (result.size() > 0) {
				scope = result.get(0);
			}
		} else {
			// Assume we're in a containing scope
			while (scope != null && 
					scope.getType() != SVDBItemType.ClassDecl &&
					scope.getType() != SVDBItemType.Covergroup &&
					scope.getType() != SVDBItemType.Coverpoint) {
				fLog.debug("Searching up-scope (current is " + scope.getType() + 
						" " + ((ISVDBNamedItem)scope).getName() + ")");
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
		while (scope != null) {
			fLog.debug("Searching scope \"" + ((ISVDBNamedItem)scope).getName() + "\"");
			for (ISVDBItemBase it : scope.getChildren()) {
				boolean matches = (types.length == 0);
				
				for (SVDBItemType type : types) {
					if (it.getType() == type) {
						matches = true;
						break;
					}
				}

				if (matches) {
					if (fMatcher.match((ISVDBNamedItem)it, id)) {
						ret.add(it);
					}
				}
			}

			// Always match exact
			SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIterator, fDefaultMatcher);
			if (((SVDBClassDecl)scope).getSuperClass() != null) {
				scope = finder.find((SVDBClassDecl)scope);
				if (scope != null) {
					fLog.debug("Find super-class \"" + 
						((SVDBClassDecl)scope).getSuperClass() + "\" returns " + scope);
				}
			} else {
				fLog.debug("No super-class");
				scope = null;
			}
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
				for (SVDBVarDeclItem vi : it.getVarList()) {
					if (fMatcher.match(vi, id)) {
						items.add(vi);
					}
				}
			}
		}
		
		for (ISVDBItemBase it : scope.getItems()) {
			for (SVDBItemType type : types) {
				if (it.getType() == type) {
					matches = true;
					break;
				}
			}
			
			if (matches) {
				if (fMatcher.match((ISVDBNamedItem)it, id)) {
					items.add(it);
				}
			}
		}
	}
}
