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


package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBFindNamedModIfcClassIfc {
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBFindNameMatcher		fMatcher;
	private List<SVDBDeclCacheItem>		fRet;
	
	public SVDBFindNamedModIfcClassIfc(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIt = index_it;
		fMatcher = matcher;
	}

	public SVDBFindNamedModIfcClassIfc(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}
	
	public synchronized List<SVDBDeclCacheItem> findCacheItems(String type_name) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		
		fRet = ret;
		
		List<SVDBDeclCacheItem> found = fIndexIt.findGlobalScopeDecl(
				new NullProgressMonitor(), type_name, fMatcher);
		
		for (SVDBDeclCacheItem ci : found) {
			if (ci.getType().isElemOf(SVDBItemType.ClassDecl, 
					SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl)) {
				ret.add(ci);
			}
		}
		
		return ret;
	}

	public synchronized List<ISVDBChildItem> findItems(String type_name) {
		List<SVDBDeclCacheItem> found = findCacheItems(type_name);
		List<ISVDBChildItem> ret = new ArrayList<ISVDBChildItem>();
	
		
		
		for (SVDBDeclCacheItem ci : found) {
			ret.add((ISVDBChildItem)ci.getSVDBItem());
		}

		return ret;
	}

}
