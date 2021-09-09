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


package org.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;

public class SVDBFindIncludedFile {
	
	private ISVDBIndexIterator				fIndexIterator;
	private ISVDBFindNameMatcher			fMatcher;
	
	public SVDBFindIncludedFile(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}
	
	public SVDBFindIncludedFile(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
	}
	
	public List<SVDBFile> find(String name) {
		/*
		ISVDBItemIterator item_it = fIndexIterator.getItemIterator(new NullProgressMonitor());
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			
			if (it.getType() == SVDBItemType.File) {
				
				if (fMatcher.match((SVDBFile)it, name)) {
					ret.add((SVDBFile)it);
				}
			}
		}
		
		return ret;
		 */
		List<SVDBDeclCacheItem> result = fIndexIterator.findGlobalScopeDecl(
				new NullProgressMonitor(), name, fMatcher);
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		for (SVDBDeclCacheItem ci : result) {
			ISVDBItemBase it = ci.getSVDBItem();
			
			if (it != null && 
					it.getType() == SVDBItemType.File) {
				ret.add((SVDBFile)it);
			}
		}
		
		return ret;
	}

}
