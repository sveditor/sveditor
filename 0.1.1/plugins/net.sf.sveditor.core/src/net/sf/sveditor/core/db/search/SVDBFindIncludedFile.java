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

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBFindIncludedFile {
	
	private ISVDBIndexIterator				fIndexIterator;
	private ISVDBFindNameMatcher			fMatcher;
	
	public SVDBFindIncludedFile(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
	}
	
	public List<SVDBFile> find(String name) {
		ISVDBItemIterator<SVDBItem> item_it = fIndexIterator.getItemIterator();
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getType() == SVDBItemType.File) {
				
				if (fMatcher.match(it, name)) {
					ret.add((SVDBFile)it);
				}
			}
		}
		
		return ret;
	}

}
