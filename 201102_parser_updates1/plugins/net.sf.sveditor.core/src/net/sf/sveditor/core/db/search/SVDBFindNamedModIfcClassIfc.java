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

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

import org.eclipse.core.runtime.NullProgressMonitor;

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

	public List<ISVDBChildItem> find(String type_name) {
		ISVDBItemIterator item_it = fIndexIt.getItemIterator(new NullProgressMonitor());
		List<ISVDBChildItem> ret = new ArrayList<ISVDBChildItem>();
		
		while (item_it.hasNext()) {
			boolean had_next = item_it.hasNext();
			ISVDBItemBase it = item_it.nextItem();
			
			if (it == null) {
				System.out.println("it == null ; hasNext=" + had_next);
			}
			
			if ((it.getType() == SVDBItemType.ClassDecl ||
					it.getType() == SVDBItemType.ModuleDecl ||
					it.getType() == SVDBItemType.InterfaceDecl)) {
				if (fMatcher.match((ISVDBNamedItem)it, type_name)) {
					ret.add((ISVDBChildItem)it);
				}
			}
		}
		
		return ret;
	}

}
