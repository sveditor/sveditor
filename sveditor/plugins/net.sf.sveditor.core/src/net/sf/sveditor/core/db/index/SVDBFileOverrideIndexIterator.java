/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileOverrideIndexIterator 
		implements ISVDBIndexIterator, ILogLevel {
	private ISVDBIndex				fIndex;
	private SVDBFile				fFile;
	private ISVDBIndexIterator		fSuperIterator;
	private LogHandle				fLog;
	
	public SVDBFileOverrideIndexIterator(SVDBFile file) {
		fFile = file;
		fLog = LogFactory.getLogHandle(getClass().getName());
	}
	
	public void setIndex(ISVDBIndex index) {
		fIndex = index;
	}
	
	public void setIndexIt(ISVDBIndexIterator index_it) {
		fSuperIterator = index_it;
	}

	public void setFile(SVDBFile file) {
		fFile = file;
	}
	
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name, 
			ISVDBFindNameMatcher 	matcher) {
		List<SVDBDeclCacheItem> ret = fSuperIterator.findGlobalScopeDecl(monitor, name, matcher);

		// First, remove any results from this file
		for (int i=0; i<ret.size(); i++) {
			if (ret.get(i) == null) {
				System.out.println("Element " + i + " is null");
			}
			if (ret.get(i).getFile() == null) {
				System.out.println("Element " + i + " has null file");
				continue;
			} else if (ret.get(i).getFile().getFilePath() == null) {
				System.out.println("Element filepath " + i + " has null file");
				continue;
			}
			if (fFile == null) {
				System.out.println("fFile == null");
			}
			if (fFile.getFilePath() == null) {
				System.out.println("getFilePath == null");
			}
			String filepath = ret.get(i).getFile().getFilePath();
			String filepath_f = fFile.getFilePath();
			if (filepath != null && filepath.equals(filepath_f)) {
				fLog.debug(LEVEL_MID, "Remove item \"" + ret.get(i).getName() + "\" because from active file");
				ret.remove(i);
				i--;
			}
		}
		
		// Okay, now do a local search from the overriding file
		findDecl(ret, fFile, name, matcher);
		
		return ret;
	}
	
	public List<SVDBRefCacheItem> findReferences(
			IProgressMonitor			monitor,
			String						name,
			ISVDBRefMatcher				matcher) {
		// TODO: Skip searching the local file for now
		return fSuperIterator.findReferences(monitor, name, matcher);
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		return fSuperIterator.getFileList(monitor);
	}
	
	private void findDecl(
			List<SVDBDeclCacheItem> 	result, 
			ISVDBChildParent 			scope,
			String						name,
			ISVDBFindNameMatcher		matcher) {
		for (ISVDBChildItem item : scope.getChildren()) {
			if (item.getType().isElemOf(SVDBItemType.PackageDecl,
					SVDBItemType.Function, SVDBItemType.Task,
					SVDBItemType.ClassDecl, SVDBItemType.ModuleDecl, 
					SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl, 
					SVDBItemType.TypedefStmt, SVDBItemType.MacroDef)) {
				if (item instanceof ISVDBNamedItem) {
					boolean is_ft = item.getType().isElemOf(
							SVDBItemType.MacroDef);
					ISVDBNamedItem ni = (ISVDBNamedItem)item;
					if (matcher.match(ni, name)) {
						fLog.debug(LEVEL_MID, "Add item \"" + ni.getName() + "\" to result");
						result.add(new SVDBDeclCacheItem(this, fFile.getFilePath(), 
								ni.getName(), ni.getType(), is_ft));
					}
				}
				if (item.getType() == SVDBItemType.PackageDecl) {
					findDecl(result, (ISVDBChildParent)item, name, matcher);
				}
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				findDecl(result, (ISVDBChildParent)item, name, matcher);
			}
		}
	}
	
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		// TODO: fixme sometimes
		return fSuperIterator.findPackageDecl(monitor, pkg_item);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		if (item.getFilename().equals(fFile.getFilePath())) {
			return fFile;
		} else {
			return fSuperIterator.getDeclFile(monitor, item);
		}
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		if (fSuperIterator != null) {
			ISVDBItemIterator super_it = fSuperIterator.getItemIterator(monitor);
			if (super_it instanceof SVDBIndexCollectionItemIterator) {
				SVDBIndexCollectionItemIterator it = (SVDBIndexCollectionItemIterator)super_it;
				it.setOverride(fIndex, fFile);
				return it;
			} else {
				return super_it;
			}
		} else {
			return SVEmptyItemIterator;
		}
	}
	
	private ISVDBItemIterator SVEmptyItemIterator = new ISVDBItemIterator() {
		public ISVDBItemBase nextItem(SVDBItemType... type_list) { return null; }
		public boolean hasNext(SVDBItemType... type_list) { return false; }
	};
}

