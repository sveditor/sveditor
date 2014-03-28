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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBPackageItemFinder {
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBFindNameMatcher		fMatcher;
	
	public SVDBPackageItemFinder(
			ISVDBIndexIterator		index_it,
			ISVDBFindNameMatcher 	matcher) {
		fIndexIt = index_it;
		fMatcher = matcher;
	}
	
	public List<SVDBItem> find(
			SVDBPackageDecl 	pkg, 
			String 				name) {
		SVDBFindIncludedFile inc_finder = new SVDBFindIncludedFile(fIndexIt);
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (ISVDBItemBase it : pkg.getChildren()) {
			if (it.getType() == SVDBItemType.Include) {
				List<SVDBFile> file = inc_finder.find(((SVDBInclude)it).getName());
				
				if (file.size() > 0) {
					find(file.get(0), ret, name);
				}
			} else if (it.getType() == SVDBItemType.ClassDecl) {
				if (fMatcher.match((SVDBModIfcDecl)it, name)) {
					ret.add((SVDBModIfcDecl)it);
				}
			}
		}
		
		
		return ret;
	}
	
	private void find(SVDBFile file, List<SVDBItem> items, String name) {
		for (ISVDBItemBase it : file.getChildren()) {
			if (it.getType() == SVDBItemType.ClassDecl) {
				if (fMatcher.match((SVDBModIfcDecl)it, name)) {
					items.add((SVDBModIfcDecl)it);
				}
			}
		}
	}

}
