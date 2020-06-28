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


package net.sf.sveditor.core.db.utils;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBIndexSearcher {
	private Map<ISVDBIndex, Set<String>>	fIndexMap;

	public SVDBIndexSearcher() {
	}
	
	public SVDBIndexSearcher(ISVDBIndex index) {
		Set<String> filelist = new HashSet<String>();
		for (String path : index.getFileList(new NullProgressMonitor())) {
			filelist.add(path);
		}
		fIndexMap.put(index, filelist);
	}

	public void addIndex(ISVDBIndex index) {
		Set<String> filelist = new HashSet<String>();
		for (String path : index.getFileList(new NullProgressMonitor())) {
			filelist.add(path);
		}
		fIndexMap.put(index, filelist);
	}
	
	/**
	public void addFile(SVDBFile file) {
		fFiles.add(file);
	}
	 */
	
	/**
	 * Finds all classes named 'name' 
	 * 
	 * @param name
	 * @return
	 */
	public SVDBClassDecl findNamedClass(String name) {
		SVDBClassDecl c;
		
		for (Entry<ISVDBIndex, Set<String>> e : fIndexMap.entrySet()) {
			for (String fname : e.getValue()) {
				SVDBFile f = e.getKey().findFile(fname);
				if ((c= findNamedClass(name, f)) != null) {
					return c;
				}
			}
		}

		return null;
	}
	
	private SVDBClassDecl findNamedClass(String name, SVDBScopeItem parent) {
		for (ISVDBItemBase it : parent.getChildren()) {
			if (it.getType() == SVDBItemType.ClassDecl && 
					((ISVDBNamedItem)it).getName() != null &&
					((ISVDBNamedItem)it).getName().equals(name)) {
				return (SVDBClassDecl)it;
			} else if (it.getType() == SVDBItemType.PackageDecl) {
				SVDBClassDecl c;
				
				if ((c = findNamedClass(name, (SVDBScopeItem)it)) != null) {
					return c;
				}
			}
		}
		
		return null;
	}
	
	public SVDBClassDecl findSuperClass(SVDBClassDecl cls) {
		if (cls.getSuperClass() != null) {
			return findNamedClass(cls.getSuperClass().getName());
		} else {
			return null;
		}
	}
	
	/**
	 * Traverses scopes beginning with 'context' searching
	 * for items named 'name'
	 * 
	 * @param name
	 * @param context
	 * @return
	 */
	public List<ISVDBItemBase> findVarsByNameInScopes(
			String				name,
			ISVDBChildItem		context,
			boolean				stop_on_first_match) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();


		// Search up the scope
		while (context != null) {
			
			// First, search the local variables
			if (context instanceof ISVDBScopeItem) {
				for (ISVDBItemBase it : ((ISVDBScopeItem)context).getItems()) {
					if (SVDBStmt.isType(it, SVDBItemType.VarDeclStmt)) {
						if (((ISVDBNamedItem)it).getName().equals(name)) {
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
			if (context.getType() == SVDBItemType.Function || 
					context.getType() == SVDBItemType.Task) {
				for (ISVDBItemBase it : ((SVDBTask)context).getParams()) {
					if (SVDBItem.getName(it).equals(name)) {
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

			context = context.getParent();
		}
		
		return ret;
	}
	
	/**
	 * Traverses scopes beginning with 'context' searching
	 * for items named 'name'
	 * 
	 * @param name
	 * @param context
	 * @return
	 */
	public List<ISVDBItemBase> findByNameInScopes(
			String				name,
			ISVDBChildItem		context,
			boolean				stop_on_first_match,
			SVDBItemType	... types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();


		// Search up the scope
		while (context != null) {
			
			// First, search the local variables
			if (context instanceof ISVDBScopeItem) {
				for (ISVDBItemBase it : ((ISVDBScopeItem)context).getItems()) {
					if (it instanceof ISVDBNamedItem && 
							((ISVDBNamedItem)it).getName().equals(name)) {
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
			if (context.getType() == SVDBItemType.Function || 
					context.getType() == SVDBItemType.Task) {
				for (ISVDBItemBase it : ((SVDBTask)context).getParams()) {
					if (SVDBItem.getName(it).equals(name)) {
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

			context = context.getParent();
		}
		
		return ret;
	}

	public List<ISVDBItemBase> findByName(
			String				name,
			SVDBItemType	...	types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		for (Entry<ISVDBIndex, Set<String>> e : fIndexMap.entrySet()) {
			for (String fname : e.getValue()) {
				SVDBFile f = e.getKey().findFile(fname);
				List<ISVDBItemBase> r = SVDBSearchUtils.findItemsByName(f, name, types);
				ret.addAll(r);
			}
		}
		
		return ret;
	}

	public List<ISVDBItemBase> findByPrefixInTypeHierarchy(
			String						prefix,
			SVDBScopeItem				ref_type,
			Comparator<String>			comparator,
			SVDBItemType		... 	types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		while (ref_type != null) {
			for (ISVDBItemBase it : ref_type.getChildren()) {
				boolean type_match = (types.length == 0);
				
				for (SVDBItemType type : types) {
					if (it.getType() == type) {
						type_match = true;
						break;
					}
				}
				
				if (type_match && (it instanceof ISVDBNamedItem) &&
						((ISVDBNamedItem)it).getName().toLowerCase().startsWith(prefix)) {
					ret.add(it);
				}
			}
			
			// Continue traversing the type hierarchy
			if (ref_type.getType() == SVDBItemType.ClassDecl &&
					((SVDBClassDecl)ref_type).getSuperClass() != null) {
				ref_type = findNamedClass(
						((SVDBClassDecl)ref_type).getSuperClass().getName());
			} else {
				ref_type = null;
			}
		}
		
		return ret;
	}

	// public List<SVDBItem> findByNameInScopeHierarchy(
			
	
	public List<ISVDBItemBase> findByNameInClassHierarchy(
			String				name,
			ISVDBChildItem		scope,
			SVDBItemType	...	types) {

		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		while (scope != null && scope.getType() != SVDBItemType.ClassDecl) {
			scope = scope.getParent();
		}
		
		if (scope == null) {
			return ret;
		}
		
		// Now, search through the scope and the class hierarchy
		while (scope != null) {
			if (scope instanceof ISVDBScopeItem) {
				for (ISVDBItemBase it : ((ISVDBScopeItem)scope).getItems()) {
					boolean match_type = (types.length == 0);

					for (SVDBItemType t : types) {
						if (it.getType() == t) {
							match_type = true;
							break;
						}
					}
					if (match_type && it instanceof ISVDBNamedItem &&
							((ISVDBNamedItem)it).getName().equals(name)) {
						ret.add(it);
					}
				}
			}
			
			scope = findNamedClass(((SVDBClassDecl)scope).getSuperClass().getName()); 
		}
		
		return ret;
	}
	
}
