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
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.parser.SVDBClassDecl;

import org.eclipse.core.runtime.NullProgressMonitor;

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

	public List<SVDBClassDecl> find(String type_name) {
		ISVDBItemIterator item_it = fIndexIt.getItemIterator(new NullProgressMonitor());
		List<SVDBClassDecl> ret = new ArrayList<SVDBClassDecl>();
		
		while (item_it.hasNext()) {
			boolean had_next = item_it.hasNext();
			ISVDBItemBase it = item_it.nextItem();
			
			if (it == null) {
				System.out.println("it == null ; hasNext=" + had_next);
			}
			
			if (it.getType() == SVDBItemType.Class) {
				if (fMatcher.match((ISVDBNamedItem)it, type_name)) {
					ret.add((SVDBClassDecl)it);
				}
			}
		}
		
		return ret;
	}

}
