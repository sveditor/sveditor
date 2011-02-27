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
import net.sf.sveditor.core.db.stmt.SVDBStmt;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBFindByName {
	private ISVDBIndexIterator			fIndexIterator;
	private ISVDBFindNameMatcher		fMatcher;
	
	public SVDBFindByName(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}
	
	public SVDBFindByName(ISVDBIndexIterator index_it, ISVDBFindNameMatcher matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
	}
	
	public List<ISVDBItemBase> find(String name, SVDBItemType ... types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		ISVDBItemIterator item_it = fIndexIterator.getItemIterator(new NullProgressMonitor());
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			
			boolean type_match = (types.length == 0);
			
			for (SVDBItemType t : types) {
				if (it.getType() == t) {
					type_match = true;
					break;
				}
			}
			
			if (type_match) {
				if (it instanceof ISVDBNamedItem) {
					if (fMatcher.match((ISVDBNamedItem)it, name)) {
						ret.add(it);
					}
				}
			}
		}
		
		return ret;
	}

}
