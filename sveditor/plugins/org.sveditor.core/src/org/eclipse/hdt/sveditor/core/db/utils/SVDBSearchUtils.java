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


package org.eclipse.hdt.sveditor.core.db.utils;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.stmt.ISVDBBodyStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBIfStmt;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVDBSearchUtils implements ILogLevel {
	
	private static final LogHandle		fLog;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBSearchUtils");
	}
	
	/**
	 * Searches the given scope for children of a given type.  The
	 * types are a comma-separated list of types
	 * 
	 * @param scope
	 * @param types
	 * @return
	 */
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

	/**
	 * Traverses UP the database, looking for the first class that it finds and then returns
	 * 
	 * @param scope
	 * @return
	 */
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
			long end_loc = ((ISVDBScopeItem)it).getEndLocation(); 
			ISVDBScopeItem s_it = (ISVDBScopeItem)it;
			debug("        start_loc=" + SVDBLocation.toString(s_it.getLocation()) + 
					" ; end_loc=" + SVDBLocation.toString(end_loc) +
					" " + SVDBItem.getName(it));
			if (s_it.getLocation() != -1 && end_loc != -1) {
				debug("    sub-scope " + SVDBItem.getName(it) + " @ " + 
						SVDBLocation.unpackLineno(it.getLocation()) + "-" + 
						((end_loc != -1)?SVDBLocation.unpackLineno(end_loc):-1));
				if (lineno >= SVDBLocation.unpackLineno(s_it.getLocation()) && 
						lineno <= SVDBLocation.unpackLineno(end_loc)) {
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
	public static ISVDBItemBase findActiveStructItem(
			ISVDBItemBase 		it, 
			int 				lineno) {
		return findActiveStructItem(it, lineno, null, null, null);
	}
	
	public static ISVDBItemBase findActiveStructItem(
			ISVDBItemBase 		it, 
			int 				lineno,
			Set<SVDBItemType>	do_not_recurse_scopes,
			Set<SVDBItemType>	expand_inline_items,
			Set<SVDBItemType>	ignore_items
			) {
		ISVDBItemBase ret = null;
		long it_loc = it.getLocation();
		
		debug("--> findActiveStructItem it=" + it + " name=" + SVDBItem.getName(it) + " lineno=" + lineno);
		
		if (it_loc != -1 && lineno >= SVDBLocation.unpackLineno(it_loc)) {
			if (it instanceof ISVDBChildParent) {
				// The goal is to find the nearest child
				Iterator<ISVDBChildItem> it_ii = ((ISVDBChildParent)it).getChildren().iterator();
				ISVDBItemBase it_i=null, it_n = null;
				
				debug("  it instanceof ISVDBChildParent");
				
				while (it_n != null || it_ii.hasNext()) {
					if (it_n != null) {
						it_i = it_n;
					} else {
						it_i = it_ii.next();
					}
					it_n = (it_ii.hasNext())?it_ii.next():null;
					debug("  it_i=" + it_i + " (" + SVDBItem.getName(it_i) + ") it_n=" + it_n +
							" (" + SVDBItem.getName(it_n) + ")");
					
					long it_i_loc = it_i.getLocation();
					long it_n_loc = (it_n != null)?it_n.getLocation():-1;
					
					if (it_i_loc != -1 && lineno < SVDBLocation.unpackLineno(it_i_loc)) {
						// We've passed where we should be
						debug("  Past valid items: it_i_loc=" + SVDBLocation.unpackLineno(it_i_loc));
						break;
					} else if (it_n_loc != -1 && lineno < SVDBLocation.unpackLineno(it_n_loc)) {
						// it_i is the one, since it_n is beyond where we are
						debug("  it_n is beyond target: it_n_loc=" + SVDBLocation.unpackLineno(it_n_loc));
						ret = it_i;
						break;
					} else if (it_n == null && it_i_loc != -1 && lineno >= SVDBLocation.unpackLineno(it_i_loc)) {
						debug("  Reached scope end: it_i_loc=" + SVDBLocation.unpackLineno(it_i_loc));
						ret = it_i;
						break;
					}
				}
			
				if (ret != null && 
						(do_not_recurse_scopes == null || !do_not_recurse_scopes.contains(ret.getType()))) {
					debug("  --> Trying sub-call ret=" + ret + " (" + SVDBItem.getName(ret) + ")");
					ISVDBItemBase sub_i = findActiveStructItem(ret, lineno, do_not_recurse_scopes, expand_inline_items, ignore_items);
					debug("  <-- Trying sub-call ret=" + sub_i);
					
					if (sub_i != null) {
						if (ignore_items == null || !ignore_items.contains(sub_i.getType())) {
							if (expand_inline_items == null || !expand_inline_items.contains(sub_i.getType())) {
								ret = sub_i;
							}
						}
					}
				}
			}
		}
		
		debug("<-- findActiveStructItem it=" + it + " name=" + SVDBItem.getName(it) + 
				" lineno=" + lineno + " ret=" + ret + " ret_name=" + SVDBItem.getName(ret));
		return ret;
	}
	

	/*
	public static ISVDBItemBase findActiveStructItem(ISVDBChildParent scope, int lineno) {
		ISVDBItemBase ret = null;
		debug("findActiveStructItem: " + SVDBItem.getName(scope) + " " + lineno);
		Iterator<ISVDBChildItem> it_i = scope.getChildren().iterator();
//		for (ISVDBItemBase it : scope.getChildren()) {
		ISVDBItemBase it=null, it_n=null;
		while (it_i.hasNext()) {
			if (it_n != null) {
				it = it_n;
			} else {
				it = it_i.next();
			}
			it_n = (it_i.hasNext())?it_i.next():null;
			
			debug("    Child: " + SVDBItem.getName(it) + " " + (it instanceof ISVDBScopeItem));
			
			if (it instanceof ISVDBBodyStmt && 
					((ISVDBBodyStmt)it).getBody() != null &&
					((ISVDBBodyStmt)it).getBody() instanceof ISVDBScopeItem) {
				it = ((ISVDBBodyStmt)it).getBody();
				debug("        instanceof ISVDBBodyStmt: child=" + SVDBItem.getName(it));
				if ((ret = findActiveStructItem_i((ISVDBScopeItem)it, lineno)) != null) {
					break;
				}
			} else if (it instanceof ISVDBEndLocation) {
				debug("        instanceof ISVDBEndLocation: child=" + SVDBItem.getName(it));
				SVDBLocation st_loc = it.getLocation();
				SVDBLocation end_loc = ((ISVDBEndLocation)it).getEndLocation();
				
				if (st_loc != null && end_loc != null && 
						lineno >= st_loc.getLine() && lineno <= end_loc.getLine()) {
					if (it instanceof ISVDBChildParent && 
							(ret = findActiveStructItem((ISVDBChildParent)it, lineno)) != null) {
						break;
					} else {
						ret = it;
						break;
					}
				}
			} else {
				debug("        default case: child=" + SVDBItem.getName(it) + " " + it);
				debug("            it=" + it + " it_n=" + it_n);
				SVDBLocation it_loc = it.getLocation();
				
				if (it_loc != null && lineno >= it_loc.getLine()) {
					if (it_n != null && it_n.getLocation() != null && ) {
						SVDBLocation it_n_loc = it_n.getLocation();
					
						if (it_n_loc != null && lineno <= it_n_loc.getLine()) {
							// Drill in to see 
						}
						if ((ret = findActiveStructItem_i(it, it_n, lineno)) != null) {
							break;
						}
					} else if (scope instanceof ISVDBChildParent) {
						SVDBLocation end_loc = 
					}

					if (scope instanceof ISVDBEndLocation) {
						SVDBLocation end_loc = ((ISVDBEndLocation)scope).getEndLocation();
						if (it_loc != null && end_loc != null &&
							lineno <= end_loc.getLine()) {
							ret = it;
							break;
						}
					} else if (scope instanceof ISVDBChildParent) {
						ISVDBItemBase it2;
						
						if ((it2 = findActiveScope((ISVDBChildParent)it, lineno)) != null) {
							ret = it2;
						}
					} else {
						ret = it;
						break;
					}
				}
			}
		}
		
		return ret;
	}
	 */

	/**
	 * Assumptions:
	 * - it is not a Scope
	 * - it_n may be a scope
	 * 
	 * @param it
	 * @param it_n
	 * @param lineno
	 * @return
	 */
//	private static ISVDBItemBase findActiveStructItem_i(ISVDBItemBase it, ISVDBItemBase it_n, int lineno) {
//		ISVDBItemBase ret = null;
//	
//		if (it_n != null) {
//			SVDBLocation it_loc = it.getLocation();
//			SVDBLocation it_n_loc = it_n.getLocation();
//			
//			debug("line=" + lineno + " it_loc=" + it_loc + " it_n_loc=" + it_n_loc);
//			
//			if (it_loc != null && it_n_loc != null) {
//				if (lineno >= it_loc.getLine() && lineno < it_n_loc.getLine()) {
//					ret = it;
//				} else if (lineno >= it_n_loc.getLine()) {
//					ret = it_n;
//				}
//			} 
//		} else if (it instanceof ISVDBEndLocation) {
//			// No next -- it must be a scope
//			SVDBLocation end_loc = ((ISVDBEndLocation)it).getEndLocation(); 
//			SVDBLocation st_loc = it.getLocation();
//			debug("        start_loc=" + st_loc + " ; end_loc=" + end_loc);
//			if (st_loc != null && end_loc != null) {
//				debug("    sub-scope " + SVDBItem.getName(it) + " @ " + 
//						st_loc + "-" + ((end_loc != null)?end_loc.getLine():-1));
//				if (lineno >= st_loc.getLine() && lineno <= end_loc.getLine()) {
//					ret = it;
//					
//					if (it instanceof ISVDBScopeItem) {
//						ISVDBItemBase s_it_p = findActiveStructItem(
//								(ISVDBScopeItem)it, lineno);
//
//						if (s_it_p != null) {
//							ret = s_it_p;
//						}
//					}
//				}
//			}			
//		}
//		
//		if (ret != null && ret instanceof ISVDBChildParent) {
//			ISVDBItemBase ret2 = null;
//		
//			if ((ret2 = findActiveStructItem((ISVDBChildParent)ret, lineno)) != null) {
//				ret = ret2;
//			}
//		}
//		
//		return ret;
//	}

	private static ISVDBItemBase findActiveStructItem_i(ISVDBScopeItem s_it, int lineno) {
		long end_loc = s_it.getEndLocation(); 
		debug("        start_loc=" + s_it.getLocation() + " ; end_loc=" + end_loc);
		if (s_it.getLocation() != -1 && end_loc != -1) {
			debug("    sub-scope " + SVDBItem.getName(s_it) + " @ " + 
					SVDBLocation.unpackLineno(s_it.getLocation()) + "-" + 
					((end_loc != -1)?SVDBLocation.unpackLineno(end_loc):-1));
			if (lineno >= SVDBLocation.unpackLineno(s_it.getLocation()) && 
					lineno <= SVDBLocation.unpackLineno(end_loc)) {
				ISVDBItemBase s_it_p = findActiveStructItem(s_it, lineno);

				if (s_it_p != null) {
					return s_it_p;
				} else {
					return s_it;
				}
			}
		}
		return null;
	}
	
	private static void debug(String msg) {
		fLog.debug(LEVEL_MAX, msg);
	}
}
