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


package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * Implements an item iterator that operates on a list of index iterators
 * 
 * @author ballance
 *
 */
public class SVDBIndexListIterator implements ISVDBIndexIterator {
	
	private List<ISVDBIndexIterator>			fIndexIteratorList;
	
	private static final class IteratorListItemIterator implements ISVDBItemIterator {
		
		private Iterator<ISVDBIndexIterator>		fIterator;
		private ISVDBItemIterator					fCurrent;
		private IProgressMonitor					fMonitor;
		
		public IteratorListItemIterator(Iterator<ISVDBIndexIterator> it, IProgressMonitor monitor) {
			fIterator = it;
			fMonitor = monitor;
		}

		public boolean hasNext(SVDBItemType... type_list) {
			while (fCurrent != null || fIterator.hasNext()) {
				
				if (fCurrent == null) {
					fCurrent = fIterator.next().getItemIterator(fMonitor);
				}
				
				if (!fCurrent.hasNext(type_list)) {
					fCurrent = null;
					continue;
				} else {
					break;
				}
			}
			
			return (fCurrent != null && fCurrent.hasNext(type_list));
		}

		public ISVDBItemBase nextItem(SVDBItemType... type_list) {
			ISVDBItemBase ret = null;
			
			while (fCurrent != null || fIterator.hasNext()) {
				
				if (fCurrent == null) {
					fCurrent = fIterator.next().getItemIterator(fMonitor);
				}
				
				if ((ret = fCurrent.nextItem(type_list)) == null) {
					fCurrent = null;
					continue;
				} else {
					break;
				}
			}
			
			return ret;
		}
	}
	
	public SVDBIndexListIterator() {
		fIndexIteratorList = new ArrayList<ISVDBIndexIterator>();
	}
	
	public void addIndexIterator(ISVDBIndexIterator it) {
		fIndexIteratorList.add(it);
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		return new IteratorListItemIterator(fIndexIteratorList.iterator(), monitor);
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (ISVDBIndexIterator index_it : fIndexIteratorList) {
			List<SVDBDeclCacheItem> tmp = index_it.findGlobalScopeDecl(monitor, name, matcher);
			ret.addAll(tmp);
		}
		return ret;
	}

	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (ISVDBIndexIterator index_it : fIndexIteratorList) {
			List<SVDBDeclCacheItem> tmp = index_it.findPackageDecl(monitor, pkg_item);
			ret.addAll(tmp);
		}
		return ret;
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		for (ISVDBIndexIterator index_it : fIndexIteratorList) {
			SVDBFile tmp = index_it.getDeclFile(monitor, item);
			if (tmp != null) {
				return tmp;
			}
		}
		return null;
	}

}
