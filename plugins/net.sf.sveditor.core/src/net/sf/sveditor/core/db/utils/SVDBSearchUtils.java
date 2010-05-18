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

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBSearchUtils {
	
	private static boolean			fDebugEn = false;
	
	public static List<SVDBItem> findItemsByType(
			SVDBScopeItem			scope,
			SVDBItemType	...		types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : scope.getItems()) {
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
	
	public static SVDBModIfcClassDecl findClassScope(SVDBScopeItem scope) {
		while (scope != null && scope.getType() != SVDBItemType.Class) {
			scope = scope.getParent();
		}
		
		return (SVDBModIfcClassDecl)scope;
	}

	public static List<SVDBItem> findItemsByName(
			SVDBScopeItem			scope,
			String					name,
			SVDBItemType	...		types) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : scope.getItems()) {
			boolean type_match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					type_match = true;
					break;
				}
			}
			
			if (type_match && it.getName() != null && it.getName().equals(name)) {
				ret.add(it);
			} else if (it instanceof SVDBScopeItem) {
				ret.addAll(findItemsByName((SVDBScopeItem)it, name, types));
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
	public static SVDBScopeItem findActiveScope(SVDBScopeItem scope, int lineno) {
		debug("findActiveScope: " + scope.getName() + " " + lineno);
		for (SVDBItem it : scope.getItems()) {
			if (it instanceof SVDBScopeItem) {
				SVDBLocation end_loc = ((SVDBScopeItem)it).getEndLocation(); 
				SVDBScopeItem s_it = (SVDBScopeItem)it;
				if (s_it.getLocation() != null && s_it.getEndLocation() != null) {
					debug("    sub-scope " + it.getName() + " @ " + 
							it.getLocation().getLine() + "-" + 
							((end_loc != null)?end_loc.getLine():-1));
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


	private static void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
