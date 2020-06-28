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


package net.sf.sveditor.core.srcgen;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class OverrideMethodsFinder implements ILogLevel {
	
	private SVDBClassDecl								fLeafClass;
	private Map<SVDBClassDecl, List<SVDBTask>>			fClassMap;
	private ISVDBIndexIterator							fIndexIt;
	private LogHandle									fLog;

	/*
	private class ClassComparator implements Comparator<SVDBModIfcClassDecl> {
		public int compare(SVDBModIfcClassDecl c1, SVDBModIfcClassDecl c2) {
			
			if (c1.getSuperClass() != null && 
					c1.getSuperClass().equals(c2.getSuperClass())) {
				return 1;
			} else {
				return -1;
			}
		}
	}
	 */
	
	public OverrideMethodsFinder(SVDBClassDecl leaf_class, ISVDBIndexIterator index_it) {
		fLog = LogFactory.getLogHandle("OverrideMethodsFinder");
		
		fLeafClass = leaf_class;
		fClassMap = new LinkedHashMap<SVDBClassDecl, List<SVDBTask>>();
		fIndexIt = index_it;
		
		findClasses();
	}
	
	public Set<SVDBClassDecl> getClassSet() {
		return fClassMap.keySet();
	}
	
	public List<SVDBTask> getMethods(SVDBClassDecl cls) {
		return fClassMap.get(cls);
	}
	
	private void findClasses() {
		fClassMap.clear();
		SVDBClassDecl cl = fLeafClass;
		SVDBFindSuperClass  finder_super = new SVDBFindSuperClass(
				fIndexIt, SVDBFindDefaultNameMatcher.getDefault());

		fLog.debug(LEVEL_MID, "findClasses: Root Class=" + SVDBItem.getName(cl));
		
		while (cl != null) {
			
			cl = finder_super.find(cl);
			
			if (cl != null) {
				fLog.debug(LEVEL_MID, "findClasses: Super Class=" + SVDBItem.getName(cl));
				List<SVDBTask> overrides = getClassOverrideTargets(cl);
				if (overrides.size() > 0) {
					fClassMap.put(cl, getClassOverrideTargets(cl));
				}
			}
		}
	}

	private List<SVDBTask> getClassOverrideTargets(SVDBClassDecl cls) {
		List<SVDBTask> ret = new ArrayList<SVDBTask>();
		
		for (ISVDBItemBase it : cls.getChildren()) {
			if (it.getType() == SVDBItemType.Function ||
					it.getType() == SVDBItemType.Task) {
				SVDBTask tf = (SVDBTask)it;
				if ((tf.getAttr() & SVDBTask.FieldAttr_Local) == 0) {
					if (!existsInClass(it, fLeafClass)) {
						ret.add(tf);
					}
				}
			}
		}
		
		return ret;
	}

	private boolean existsInClass(ISVDBItemBase it, SVDBClassDecl cls) {
		
		for (ISVDBItemBase it_t : cls.getChildren()) {
			if (it instanceof ISVDBNamedItem && it_t instanceof ISVDBNamedItem && 
					((ISVDBNamedItem)it_t).getName().equals(
							((ISVDBNamedItem)it).getName())) {
				return true;
			}
		}
		
		return false;
	}

}
