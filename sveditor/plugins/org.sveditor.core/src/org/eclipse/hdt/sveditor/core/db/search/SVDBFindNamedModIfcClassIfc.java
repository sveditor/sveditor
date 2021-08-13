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


package org.eclipse.hdt.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;

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

	public synchronized List<SVDBDeclCacheItem> findItems(String type_name) {
		List<SVDBDeclCacheItem> found = findCacheItems(type_name);
	
		return found;
	}

}
