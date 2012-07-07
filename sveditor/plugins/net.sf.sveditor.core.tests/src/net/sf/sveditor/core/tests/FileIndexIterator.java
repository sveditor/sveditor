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

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class FileIndexIterator extends AbstractSVDBIndex /* implements ISVDBIndexIterator  */{
	private SVDBFile				fFile;
	private SVDBFile				fPPFile;
	Map<String, SVDBFile>			fFileMap;
	
	public FileIndexIterator(SVDBFile file) {
		super("project", "base", new SVDBFSFileSystemProvider(), new InMemoryIndexCache(), null);
		fFile = file;
		fFileMap = new HashMap<String, SVDBFile>();
		
		fFileMap.put(file.getName(), file);
		init(new NullProgressMonitor());
		loadIndex(new NullProgressMonitor());
	}
	
	public FileIndexIterator(Tuple<SVDBFile, SVDBFile> file) {
		super("project", "base", new SVDBFSFileSystemProvider(), new InMemoryIndexCache(), null);
		fPPFile = file.first();
		fFile = file.second();
		fFileMap = new HashMap<String, SVDBFile>();
		
		fFileMap.put(fFile.getName(), fFile);
		init(new NullProgressMonitor());
		loadIndex(new NullProgressMonitor());
	}
	
	public String getTypeID() {
		return "FileIndexIterator";
	}

	@Override
	protected String getLogName() {
		return "FileIndexIterator";
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		addFile(fFile.getFilePath());
	}
	
	@Override
	protected void processFile(SVDBFileTree path, IPreProcMacroProvider mp) {
		// Do Nothing
	}

	@Override
	protected SVDBFile processPreProcFile(String path) {
		// Do Nothing
		cacheDeclarations(fFile);
		cacheReferences(fFile);
		getCache().setFile(fFile.getFilePath(), fFile);
		return null;
	}

	@Override
	protected void parseFiles(IProgressMonitor monitor) {
		// Do Nothing
	}

	@Override
	protected void buildFileTree(IProgressMonitor monitor) {
		// Do Nothing
	}

	@Override
	public synchronized SVDBFileTree findFileTree(String path) {
		if (fPPFile != null) {
			SVDBFileTree ft = new SVDBFileTree(
					(SVDBFile)fPPFile.duplicate());
			SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
			Map<String, SVDBFileTree> working_set = new HashMap<String, SVDBFileTree>();
			ft_utils.resolveConditionals(ft, new SVPreProcDefineProvider(
					createPreProcMacroProvider(ft, working_set)));
			return ft;
		} else {
			return null;
		}
	}
	
	/*
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
	 */

}
