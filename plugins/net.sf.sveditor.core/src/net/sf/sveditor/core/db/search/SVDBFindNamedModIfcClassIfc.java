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

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBFindNamedModIfcClassIfc {
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBFindNameMatcher		fMatcher;
	
	public SVDBFindNamedModIfcClassIfc(
			ISVDBIndexIterator 		index_it,
			ISVDBFindNameMatcher	matcher) {
		fIndexIt = index_it;
		fMatcher = matcher;
	}

	public SVDBFindNamedModIfcClassIfc(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}

	public List<SVDBModIfcClassDecl> find(String type_name) {
		ISVDBItemIterator item_it = fIndexIt.getItemIterator();
		List<SVDBModIfcClassDecl> ret = new ArrayList<SVDBModIfcClassDecl>();
		
		while (item_it.hasNext()) {
			boolean had_next = item_it.hasNext();
			SVDBItem it = item_it.nextItem();
			
			if (it == null) {
				System.out.println("it == null ; hasNext=" + had_next);
			}
			
			if ((it.getType() == SVDBItemType.Class ||
					it.getType() == SVDBItemType.Module ||
					it.getType() == SVDBItemType.Interface ||
					it.getType() == SVDBItemType.Struct)) {
				if (fMatcher.match(it, type_name)) {
					ret.add((SVDBModIfcClassDecl)it);
				}
			}
		}
		
		return ret;
	}

}
