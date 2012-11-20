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
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFindByNameInScopes {
	private ISVDBFindNameMatcher			fMatcher;
	private LogHandle						fLog;
	
	public SVDBFindByNameInScopes(ISVDBIndexIterator index_it) {
		fMatcher = SVDBFindDefaultNameMatcher.getDefault();
		fLog = LogFactory.getLogHandle("SVDBFindByNameInScopes");
	}
	
	public SVDBFindByNameInScopes(ISVDBIndexIterator index_it, ISVDBFindNameMatcher matcher) {
		fMatcher = matcher;
		fLog = LogFactory.getLogHandle("SVDBFindByNameInScopes");
	}
	
	public List<ISVDBItemBase> find(
			ISVDBChildItem			context,
			String					name,
			boolean					stop_on_first_match,
			SVDBItemType	...		types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		fLog.debug("--> find: context=" + ((context!=null)?SVDBItem.getName(context):"null") + 
				" type=" + ((context != null)?context.getType():"null") + " name=" + name);
		
		// Search up the scope
		while (context != null && context instanceof ISVDBChildParent) {
			
			if (context.getType() == SVDBItemType.ClassDecl) {
				SVDBClassDecl cls = (SVDBClassDecl)context;
				if (cls.getParameters() != null) {
					for (SVDBModIfcClassParam p : cls.getParameters()) {
						if (fMatcher.match(p, name)) {
							ret.add(p);
						}
					}
				}
			}
			
			// First, search the local variables
			for (ISVDBItemBase it : ((ISVDBChildParent)context).getChildren()) {
				fLog.debug("Scope " + SVDBItem.getName(context) + " child " + SVDBItem.getName(it));
				if (it instanceof SVDBVarDeclStmt) {
					for (ISVDBItemBase it_t : ((SVDBVarDeclStmt)it).getChildren()) {
						fLog.debug("  Variable " + SVDBItem.getName(it_t) + " (match " + name + ")");
						if (it_t instanceof ISVDBNamedItem && fMatcher.match((ISVDBNamedItem)it_t, name)) {
							boolean match = (types.length == 0 || it_t.getType().isElemOf(types));
							
							if (match) {
								fLog.debug("    Matches Variable " + SVDBItem.getName(it_t));
								ret.add(it_t);
								
								if (stop_on_first_match) {
									break;
								}
							}
						}
					}
				} else if (it instanceof SVDBModIfcInst) {
					for (ISVDBItemBase it_t : ((SVDBModIfcInst)it).getChildren()) {
						if (it_t instanceof ISVDBNamedItem && fMatcher.match((ISVDBNamedItem)it_t, name)) {
							boolean match = (types.length == 0);

							for (SVDBItemType t : types) {
								if (it_t.getType() == t) {
									match = true;
									break;
								}
							}
							
							if (match) {
								ret.add(it_t);
								
								if (stop_on_first_match) {
									break;
								}
							}
						}
					}
				} else if (it.getType() == SVDBItemType.TypedefStmt &&
						((SVDBTypedefStmt)it).getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					// Check the enumerators for matches
					SVDBTypeInfoEnum e = (SVDBTypeInfoEnum)((SVDBTypedefStmt)it).getTypeInfo();
					for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
						if (fMatcher.match(en, name)) {
							ret.add(en);
							if (stop_on_first_match) {
								break;
							}
						}
					}
					if (ret.size() > 0 && stop_on_first_match) {
						break;
					}
				} else {
					if (it instanceof ISVDBNamedItem && fMatcher.match((ISVDBNamedItem)it, name)) {
						boolean match = (types.length == 0);

						for (SVDBItemType t : types) {
							if (it.getType() == t) {
								match = true;
								break;
							}
						}
						
						if (match) {
							ret.add(it);
							
							if (stop_on_first_match) {
								break;
							}
						}
					}
				}
			}
			
			if (ret.size() > 0 && stop_on_first_match) {
				break;
			}
			
			// Next, search the parameters, if we're in a function/task scope
			if (context.getType().isElemOf(SVDBItemType.Function, SVDBItemType.Task)) {
				for (SVDBParamPortDecl p : ((SVDBTask)context).getParams()) {
					for (ISVDBChildItem pi : p.getChildren()) {
						fLog.debug("check param \"" + SVDBItem.getName(pi) + "\"");
						if (fMatcher.match((ISVDBNamedItem)pi, name)) {
							ret.add(pi);
						
							if (stop_on_first_match) {
								break;
							}
						}
					}
					if (ret.size() > 0 && stop_on_first_match) {
						break;
					}
				}
			}

			if (ret.size() > 0 && stop_on_first_match) {
				break;
			}
			
			// Next, if we check the class parameters if we're in a class scope,
			// or the module ports/parameters if we're in an interface/module scope
			fLog.debug("context type: " + context.getType());
			if (context.getType() == SVDBItemType.ClassDecl) {
//				SVDBClassDecl cls = (SVDBClassDecl)context;
				
			} else if (context.getType() == SVDBItemType.ModuleDecl ||
					context.getType() == SVDBItemType.InterfaceDecl) {
				List<SVDBParamPortDecl> p_list = ((SVDBModIfcDecl)context).getPorts();

				// Check ports
				for (SVDBParamPortDecl p : p_list) {
					for (ISVDBChildItem c : p.getChildren()) {
						SVDBVarDeclItem pi = (SVDBVarDeclItem)c;
						fLog.debug("  Check port " + pi.getName() + " == " + name);
						if (fMatcher.match((ISVDBNamedItem)pi, name)) {
							ret.add(pi);
							if (ret.size() > 0 && stop_on_first_match) {
								break;
							}
						}
						if (ret.size() > 0 && stop_on_first_match) {
							break;
						}
					}
				}
			}

			if (ret.size() > 0 && stop_on_first_match) {
				break;
			}

			while ((context = context.getParent()) != null && 
					!(context instanceof ISVDBChildParent)) { }
			
			fLog.debug("parent: " + ((context != null)?context.getType():"NULL"));
		}

		fLog.debug("<-- find: context=" + ((context!=null)?SVDBItem.getName(context):"null") + " name=" + name);

		return ret;
	}

}
