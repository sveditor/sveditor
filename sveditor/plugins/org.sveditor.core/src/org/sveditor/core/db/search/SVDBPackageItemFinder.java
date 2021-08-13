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

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBInclude;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBModIfcDecl;
import org.sveditor.core.db.SVDBPackageDecl;
import org.sveditor.core.db.index.ISVDBIndexIterator;

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
