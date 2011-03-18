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
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBSearchUtils {
	
	private static boolean			fDebugEn = false;
	
	public static List<ISVDBItemBase> findItemsByType(
			SVDBScopeItem			scope,
			SVDBItemType	...		types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		for (ISVDBItemBase it : scope.getItems()) {
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
	
	public static SVDBModIfcClassDecl findClassScope(ISVDBChildItem scope) {
		while (scope != null && scope.getType() != SVDBItemType.Class) {
			scope = scope.getParent();
		}
		
		return (SVDBModIfcClassDecl)scope;
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
	public static ISVDBScopeItem findActiveScope(ISVDBScopeItem scope, int lineno) {
		debug("findActiveScope: " + ((ISVDBNamedItem)scope).getName() + " " + lineno);
		for (ISVDBItemBase it : scope.getItems()) {
			if (it instanceof ISVDBScopeItem) {
				SVDBLocation end_loc = ((ISVDBScopeItem)it).getEndLocation(); 
				ISVDBScopeItem s_it = (ISVDBScopeItem)it;
				if (s_it.getLocation() != null && s_it.getEndLocation() != null) {
					debug("    sub-scope " + ((ISVDBNamedItem)it).getName() + " @ " + 
							it.getLocation().getLine() + "-" + 
							((end_loc != null)?end_loc.getLine():-1));
					if (lineno >= s_it.getLocation().getLine() && 
							lineno <= s_it.getEndLocation().getLine()) {
						ISVDBScopeItem s_it_p = findActiveScope(s_it, lineno);
						
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


	private static void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
