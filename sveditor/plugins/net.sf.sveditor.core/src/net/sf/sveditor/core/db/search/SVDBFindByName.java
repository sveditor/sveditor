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
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBFindByName implements ISVDBIndexOperation {
	private ISVDBIndexOperationRunner	fIndexIterator;
	private ISVDBFindNameMatcher		fMatcher;
	private LogHandle					fLog;
	private String						fName;
	private SVDBItemType				fTypes[];
	List<SVDBDeclCacheItem>				fRet;
	
	public SVDBFindByName(ISVDBIndexOperationRunner index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}
	
	public SVDBFindByName(ISVDBIndexOperationRunner index_it, ISVDBFindNameMatcher matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
		fLog = LogFactory.getLogHandle("SVDBFindByName");
	}
	
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		// TODO Auto-generated method stub
		
		List<SVDBDeclCacheItem> found = index.findGlobalScopeDecl(
				new NullProgressMonitor(), fName, fMatcher);
		
		for (SVDBDeclCacheItem item : found) {
			if (fTypes.length == 0 || item.getType().isElemOf(fTypes)) {
				if (item.getSVDBItem() != null) {
					fRet.add(item);
				} else {
					try {
						throw new Exception();
					} catch (Exception e) { 
						fLog.error("item " + item.getType() + " : " +  item.getName() + " is null", e);
					}
				}
			}
		}
	}
	public List<ISVDBItemBase> findItems(
			String 				name,
			SVDBItemType ... 	types) {
		return findItems(name, false, types);
	}
	
	public List<ISVDBItemBase> findItems(
			String 				name,
			boolean				sync,
			SVDBItemType ... 	types) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		List<SVDBDeclCacheItem> cache_items = find(name, sync, types);
		
		for (SVDBDeclCacheItem it : cache_items) {
			ret.add(it.getSVDBItem());
		}
		
		return ret;
	}
	
	public List<SVDBDeclCacheItem> findCacheItems(
			String 				name, 
			SVDBItemType ... 	types) {
		return find(name, false, types);
	}

	public List<SVDBDeclCacheItem> find(
			String 				name, 
			boolean				sync,
			SVDBItemType ... 	types) {
		fRet 	= new ArrayList<SVDBDeclCacheItem>();
		fName 	= name;
		fTypes 	= types;

		fIndexIterator.execOp(new NullProgressMonitor(), this, sync);

		return fRet;
	}

}
