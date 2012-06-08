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
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBFindByName {
	private ISVDBIndexIterator			fIndexIterator;
	private ISVDBFindNameMatcher		fMatcher;
	private LogHandle					fLog;
	
	public SVDBFindByName(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}
	
	public SVDBFindByName(ISVDBIndexIterator index_it, ISVDBFindNameMatcher matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
		fLog = LogFactory.getLogHandle("SVDBFindByName");
	}
	
	public List<ISVDBItemBase> find(String name, SVDBItemType ... types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		List<SVDBDeclCacheItem> found = fIndexIterator.findGlobalScopeDecl(
				new NullProgressMonitor(), name, fMatcher);
		
		for (SVDBDeclCacheItem item : found) {
			if (item.getType().isElemOf(types)) {
				if (item.getSVDBItem() != null) {
					ret.add(item.getSVDBItem());
				} else {
					try {
						throw new Exception();
					} catch (Exception e) { 
						fLog.error("item " + item.getType() + " : " +  item.getName() + " is null", e);
					}
				}
			}
		}
		
		return ret;
	}

}
