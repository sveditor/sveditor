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


package net.sf.sveditor.core.tests;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

import org.eclipse.core.runtime.IProgressMonitor;

public class FileIndexIterator implements ISVDBIndexIterator {
	Map<String, SVDBFile>			fFileMap;
	
	public FileIndexIterator(SVDBFile file) {
		fFileMap = new HashMap<String, SVDBFile>();
		
		fFileMap.put(file.getName(), file);
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		Set<String> path = new HashSet<String>();
		for (String elem : fFileMap.keySet()) {
			path.add(elem);
		}
		return new SVDBIndexItemIterator(path,
				new ISVDBIndex() {
					
					public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {return null;}
					public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {return null;}
					public void setIncludeFileProvider(ISVDBIncludeFileProvider inc_provider) {}
					public void setGlobalDefine(String key, String val) {}
					public void removeChangeListener(ISVDBIndexChangeListener l) {}
					public void rebuildIndex() {}
					public ISVDBIndexCache getCache() { return null; }
					public SVDBIndexConfig getConfig() { return null; }
					public SVDBFile parse(IProgressMonitor monitor, InputStream in, String path, List<SVDBMarker> markers) {
						return null;
					}
					public void setEnableAutoRebuild(boolean en) {}
					public boolean isDirty() { return false; }
					public void init(IProgressMonitor monitor) {}
					public String getTypeID() {
						return null;
					}
					public Set<String> getFileList(IProgressMonitor monitor) {
						return null;
					}
					public List<SVDBMarker> getMarkers(String path ) {
						return null;
					}
					public String getBaseLocation() {
						return null;
					}
					public String getProject() {
						return "";
					}
					public SVDBFile findPreProcFile(String path) {
						return null;
					}
					public SVDBFile findFile(String path) {
						return fFileMap.get(path);
					}
					public void dispose() {}
					public void clearGlobalDefines() {}
					public void addChangeListener(ISVDBIndexChangeListener l) {}
					public void loadIndex(IProgressMonitor monitor) {}
					
					public List<SVDBDeclCacheItem> findGlobalScopeDecl(
							IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) { return null; }
					public List<SVDBDeclCacheItem> findPackageDecl(
							IProgressMonitor monitor, SVDBDeclCacheItem pkg_item) { return null; }
					public SVDBFile getDeclFile(IProgressMonitor monitor,
							SVDBDeclCacheItem item) { return null; }
					
					
				});
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (Entry<String, SVDBFile> e : fFileMap.entrySet()) {
			for (ISVDBChildItem c : e.getValue().getChildren()) {
				if (matcher.match((ISVDBNamedItem)c, name)) {
					ret.add(new SVDBDeclCacheItem(this, e.getKey(), 
							((ISVDBNamedItem)c).getName(), c.getType()));
				}
			}
		}
		
		return ret;
	}
	
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		return null;
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		return fFileMap.keySet();
	}
	
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		return fFileMap.get(item.getFilename());
	}

}
