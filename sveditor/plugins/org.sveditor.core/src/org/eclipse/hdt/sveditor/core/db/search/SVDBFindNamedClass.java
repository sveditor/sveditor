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
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;

public class SVDBFindNamedClass {
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBFindNameMatcher		fMatcher;
	
	public SVDBFindNamedClass(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIt = index_it;
		fMatcher = matcher;
	}

	public SVDBFindNamedClass(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}

	public List<SVDBClassDecl> findItem(String type_name) {
		List<SVDBClassDecl> ret = new ArrayList<SVDBClassDecl>();
		
		List<SVDBDeclCacheItem> found = fIndexIt.findGlobalScopeDecl(
				new NullProgressMonitor(), type_name, fMatcher);
		
		for (SVDBDeclCacheItem ci : found) {
			if (ci.getType() == SVDBItemType.ClassDecl) {
				ret.add((SVDBClassDecl)ci.getSVDBItem());
			}
		}
		
		return ret;
	}

	public List<SVDBDeclCacheItem> findCacheItem(String type_name) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		
		List<SVDBDeclCacheItem> found = fIndexIt.findGlobalScopeDecl(
				new NullProgressMonitor(), type_name, fMatcher);
		
		for (SVDBDeclCacheItem ci : found) {
			if (ci.getType() == SVDBItemType.ClassDecl) {
				ret.add(ci);
			}
		}
		
		return ret;
	}
}
