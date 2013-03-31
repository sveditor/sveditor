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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

import org.eclipse.core.runtime.NullProgressMonitor;

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
