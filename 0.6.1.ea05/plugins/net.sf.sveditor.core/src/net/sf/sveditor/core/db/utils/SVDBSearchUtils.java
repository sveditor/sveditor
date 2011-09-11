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


package net.sf.sveditor.core.db.utils;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBEndLocation;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.stmt.ISVDBBodyStmt;

public class SVDBSearchUtils {
	
	private static final boolean		fDebugEn = false;
	
	public static List<ISVDBItemBase> findItemsByType(
			SVDBScopeItem			scope,
			SVDBItemType	...		types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		for (ISVDBItemBase it : scope.getChildren()) {
			boolean match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					match = true;
					break;
				}
			}
			
			if (match) {
				ret.add(it);
			}
		}
		
		return ret;
	}
	
	public static SVDBModIfcDecl findClassScope(ISVDBChildItem scope) {
		while (scope != null && scope.getType() != SVDBItemType.ClassDecl) {
			scope = scope.getParent();
		}
		
		return (SVDBModIfcDecl)scope;
	}

	public static List<ISVDBItemBase> findItemsByName(
			ISVDBScopeItem			scope,
			String					name,
			SVDBItemType	...		types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		for (ISVDBItemBase it : scope.getItems()) {
			boolean type_match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					type_match = true;
					break;
				}
			}
			
			if (type_match && (it instanceof ISVDBNamedItem) &&
					((ISVDBNamedItem)it).getName() != null && 
					((ISVDBNamedItem)it).getName().equals(name)) {
				ret.add(it);
			} else if (it instanceof ISVDBScopeItem) {
				ret.addAll(findItemsByName((ISVDBScopeItem)it, name, types));
			}
		}
		
		return ret;
	}

	/**
	 * Searches through a scope (usually an SVDBFile) to find the scope
	 * corresponding to 'lineno'. 
	 * 
	 * @param scope
	 * @param lineno
	 * @return
	 */
	public static ISVDBScopeItem findActiveScope(ISVDBChildParent scope, int lineno) {
		debug("findActiveScope: " + SVDBItem.getName(scope) + " " + lineno);
		for (ISVDBItemBase it : scope.getChildren()) {
			debug("    Child: " + SVDBItem.getName(it) + " " + (it instanceof ISVDBScopeItem));
			
			if (it instanceof ISVDBBodyStmt && 
					((ISVDBBodyStmt)it).getBody() != null &&
					((ISVDBBodyStmt)it).getBody() instanceof ISVDBScopeItem) {
				it = ((ISVDBBodyStmt)it).getBody();
			}
			
			if (it instanceof ISVDBScopeItem) {
				SVDBLocation end_loc = ((ISVDBScopeItem)it).getEndLocation(); 
				ISVDBScopeItem s_it = (ISVDBScopeItem)it;
				if (s_it.getLocation() != null && end_loc != null) {
					debug("    sub-scope " + SVDBItem.getName(it) + " @ " + 
							it.getLocation().getLine() + "-" + 
							((end_loc != null)?end_loc.getLine():-1));
					if (lineno >= s_it.getLocation().getLine() && 
							lineno <= end_loc.getLine()) {
						ISVDBScopeItem s_it_p = findActiveScope(s_it, lineno);
						
						if (s_it_p != null) {
							return s_it_p;
						} else {
							return (ISVDBScopeItem)s_it;
						}
					}
				}
			}
		}
		
		return null;
	}


	private static void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
