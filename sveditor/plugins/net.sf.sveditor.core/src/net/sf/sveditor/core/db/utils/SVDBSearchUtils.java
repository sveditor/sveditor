/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.stmt.ISVDBBodyStmt;
import net.sf.sveditor.core.db.stmt.SVDBIfStmt;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBSearchUtils implements ILogLevel {
	
	private static final LogHandle		fLog;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBSearchUtils");
	}
	
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
		ISVDBScopeItem ret = null;
		debug("findActiveScope: " + SVDBItem.getName(scope) + " " + lineno);
		for (ISVDBItemBase it : scope.getChildren()) {
			debug("    Child: " + SVDBItem.getName(it) + " " + (it instanceof ISVDBScopeItem));
			
			if (it instanceof ISVDBBodyStmt && 
					((ISVDBBodyStmt)it).getBody() != null &&
					((ISVDBBodyStmt)it).getBody() instanceof ISVDBScopeItem) {
				it = ((ISVDBBodyStmt)it).getBody();
				debug("        instanceof ISVDBBodyStmt: child=" + SVDBItem.getName(it));
				if ((ret = findActiveScope_i(it, lineno)) != null) {
					break;
				}
			} else if (it.getType() == SVDBItemType.IfStmt) {
				SVDBIfStmt if_stmt = (SVDBIfStmt)it;
				if (if_stmt.getIfStmt() != null) {
					if ((ret = findActiveScope_i(if_stmt.getIfStmt(), lineno)) != null) {
						break;
					}
				}
				if (if_stmt.getElseStmt() != null) {
					if ((ret = findActiveScope_i(if_stmt.getElseStmt(), lineno)) != null) {
						break;
					}
				}
			} else {
				if ((ret = findActiveScope_i(it, lineno)) != null) {
					break;
				}
			}
		}
		
		return ret;
	}

	private static ISVDBScopeItem findActiveScope_i(ISVDBItemBase it, int lineno) {
		if (it instanceof ISVDBScopeItem) {
			SVDBLocation end_loc = ((ISVDBScopeItem)it).getEndLocation(); 
			ISVDBScopeItem s_it = (ISVDBScopeItem)it;
			debug("        start_loc=" + s_it.getLocation() + " ; end_loc=" + end_loc);
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
		return null;
	}

	private static void debug(String msg) {
		fLog.debug(LEVEL_MAX, msg);
	}
}
