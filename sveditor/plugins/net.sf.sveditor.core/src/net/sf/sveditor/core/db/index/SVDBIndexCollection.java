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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringIterableIterator;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.ISVDBPreProcIndexSearcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBIndexCollection implements ISVDBPreProcIndexSearcher, ISVDBIndexIterator,
		ISVDBIndexOperationRunner, ISVDBIndexParse, ILogLevel {
	private SVDBIndexCollectionMgr					fMgr;
	private String									fProject;
	private List<ISVDBIndex>						fSourceCollectionList;
	private List<ISVDBIndex>						fIncludePathList;
	private List<ISVDBIndex>						fLibraryPathList;
	private List<ISVDBIndex>						fPluginLibraryList;
	private List<List<ISVDBIndex>>					fFileSearchOrder;
	private Set<String>								fProjectRefs;
	private ISVDBProjectRefProvider					fProjectRefProvider;
	private List<ISVDBIndexChangeListener>			fIndexChangeListeners;
	private LogHandle								fLog;

	// Constructor primary for testing
	public SVDBIndexCollection(String project) {
		this(null, project);
	}

	public SVDBIndexCollection(SVDBIndexCollectionMgr mgr, String project) {
		fMgr					= mgr;
		fProject 				= project;
		fSourceCollectionList 	= new ArrayList<ISVDBIndex>();
		fIncludePathList 		= new ArrayList<ISVDBIndex>();
		fLibraryPathList 		= new ArrayList<ISVDBIndex>();
		fPluginLibraryList 		= new ArrayList<ISVDBIndex>();
		fProjectRefs			= new HashSet<String>();

		fFileSearchOrder		= new ArrayList<List<ISVDBIndex>>();
		fFileSearchOrder.add(fLibraryPathList);
		fFileSearchOrder.add(fSourceCollectionList);
		fFileSearchOrder.add(fIncludePathList);
		fFileSearchOrder.add(fPluginLibraryList);
		
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		
		fLog = LogFactory.getLogHandle("IndexCollectionMgr");
		
		if (fMgr != null) {
			fMgr.addIndexCollection(this);
		}
	}
	
	public void loadIndex(IProgressMonitor monitor) {
		SubProgressMonitor sm = new SubProgressMonitor(monitor, 1);
		
		sm.beginTask("loadIndex",
				fSourceCollectionList.size() + 
				fIncludePathList.size() + 
				fLibraryPathList.size() + 
				fPluginLibraryList.size());
		
		synchronized (fSourceCollectionList) {
			for (ISVDBIndex index : fSourceCollectionList) {
				index.loadIndex(new SubProgressMonitor(sm, 1));
			}
		}
		
		synchronized (fIncludePathList) {
			for (ISVDBIndex index : fIncludePathList) {
				index.loadIndex(new SubProgressMonitor(sm, 1));
			}
		}
		
		synchronized (fLibraryPathList) {
			for (ISVDBIndex index : fLibraryPathList) {
				index.loadIndex(new SubProgressMonitor(sm, 1));
			}
		}
		
		synchronized (fPluginLibraryList) {
			for (ISVDBIndex index : fPluginLibraryList) {
				index.loadIndex(new SubProgressMonitor(sm, 1));
			}
		}
		
		sm.done();
	}
	
	public boolean isLoaded() {
		boolean loaded = true;
	
		synchronized (fSourceCollectionList) {
			for (ISVDBIndex index : fSourceCollectionList) {
				loaded &= index.isLoaded();
			}
		}
		
		synchronized (fIncludePathList) {
			for (ISVDBIndex index : fIncludePathList) {
				loaded &= index.isLoaded();
			}
		}
		
		synchronized (fLibraryPathList) {
			for (ISVDBIndex index : fLibraryPathList) {
				loaded &= index.isLoaded();
			}
		}
		
		synchronized (fPluginLibraryList) {
			for (ISVDBIndex index : fPluginLibraryList) {
				loaded &= index.isLoaded();
			}
		}
		
		return loaded;
	}
	
	public boolean isFileListLoaded() {
		boolean loaded = true;
	
		synchronized (fSourceCollectionList) {
			for (ISVDBIndex index : fSourceCollectionList) {
				loaded &= index.isFileListLoaded();
			}
		}
		
		synchronized (fIncludePathList) {
			for (ISVDBIndex index : fIncludePathList) {
				loaded &= index.isFileListLoaded();
			}
		}
		
		synchronized (fLibraryPathList) {
			for (ISVDBIndex index : fLibraryPathList) {
				loaded &= index.isFileListLoaded();
			}
		}
		
		synchronized (fPluginLibraryList) {
			for (ISVDBIndex index : fPluginLibraryList) {
				loaded &= index.isFileListLoaded();
			}
		}
		
		return loaded;
	}	
	
	/**
	 * Called by the IndexCollectionMgr when a global setting
	 * is changed
	 * 
	 */
	public void settingsChanged() {
		
	}
	
	public void addIndexChangeListener(ISVDBIndexChangeListener l) {
		if (!fIndexChangeListeners.contains(l)) {
			fIndexChangeListeners.add(l);
		}
		
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				index.addChangeListener(l);
			}
		}
	}
	
	public void removeIndexChangeListener(ISVDBIndexChangeListener l) {
		fIndexChangeListeners.remove(l);

		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				index.removeChangeListener(l);
			}
		}
	}
	
	public void dispose() {
		for (ISVDBIndex i : getIndexList()) {
			i.dispose();
		}
	}
	
	public String getProject() {
		return fProject;
	}
	
	public void rebuildIndex(IProgressMonitor monitor) {
		/*
		for (ISVDBIndex i : getIndexList()) {
			i.rebuildIndex(monitor);
		}
		 */
		monitor.beginTask("Rebuild Indexes", 1000*getIndexList().size());
		for (ISVDBIndex i : getIndexList()) {
			i.execIndexChangePlan(new SubProgressMonitor(monitor, 1000),
					new SVDBIndexChangePlanRebuild(i));
		}
		monitor.done();
	}
	
	public void clear() {
		fLog.debug("clear");
		for (ISVDBIndex index : fSourceCollectionList) {
			index.setIncludeFileProvider(null);
		}
		fSourceCollectionList.clear();
		
		for (ISVDBIndex index : fIncludePathList) {
			index.setIncludeFileProvider(null);
		}
		fIncludePathList.clear();
		
		for (ISVDBIndex index : fLibraryPathList) {
			index.setIncludeFileProvider(null);
		}
		fLibraryPathList.clear();
		
		for (ISVDBIndex index : fPluginLibraryList) {
			index.setIncludeFileProvider(null);
		}
		fPluginLibraryList.clear();
		fProjectRefs.clear();
	}
	
	public List<ISVDBIndex> getIndexList() {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			ret.addAll(i_l);
		}
		
		return ret;
	}

	public List<SVDBFilePath> getFilePath(String path) {
		List<SVDBFilePath> ret = new ArrayList<SVDBFilePath>();
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			for (ISVDBIndex index : i_l) {
				List<SVDBFilePath> p = index.getFilePath(path);
				ret.addAll(p);
			}
		}
		
		return ret;
	}

	private void getItemIterators(
			List<String>				referenced_projects,
			List<ISVDBIndexIterator>	iterator_list) {
		if (referenced_projects.contains(fProject)) {
			return;
		}
		referenced_projects.add(fProject);
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			for (ISVDBIndex index : i_l){
				iterator_list.add(index);
			}
		}
		
		if (fProjectRefProvider != null) {
			for (String proj : fProjectRefs) {
				if (!referenced_projects.contains(proj)) {
					SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(proj);
					mgr_t.getItemIterators(referenced_projects, iterator_list);
				}
			}
		}
	}
		
	public void addProjectRef(String ref) {
		if (!fProjectRefs.contains(ref)) {
			fProjectRefs.add(ref);
		}
	}
	
	public Set<String> getProjectRefs() {
		return fProjectRefs;
	}
	
	public void setProjectRefProvider(ISVDBProjectRefProvider p) {
		fProjectRefProvider = p;
	}

	public ISVDBProjectRefProvider getProjectRefProvider() {
		return fProjectRefProvider;
	}
	
	public void addSourceCollection(ISVDBIndex index) {
		fLog.debug("addSourceCollection: " + index.getBaseLocation());
		
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		fSourceCollectionList.add(index);
		
		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> getSourceCollectionList() {
		return fSourceCollectionList;
	}
	
	public void addIncludePath(ISVDBIndex index) {
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		fIncludePathList.add(index);
	}
	
	public void addLibraryPath(ISVDBIndex index) {
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		fLibraryPathList.add(index);
		
		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> getLibraryPathList() {
		return fLibraryPathList;
	}
	
	public List<ISVDBIndex> getPluginPathList() {
		return fPluginLibraryList;
	}
	
	public void addPluginLibrary(ISVDBIndex index) {
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fPluginLibraryList);
		/*
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fSourceCollectionList);
		 */
		index.setIncludeFileProvider(p);
		fPluginLibraryList.add(index);

		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> findManagingIndex(String path) {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		synchronized (fFileSearchOrder) {
			// Search the indexes in order
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					if (index.doesIndexManagePath(path)) {
						ret.add(index);
					}
				}
			}
		}
		
		return ret;
	}
	
	public List<SVDBSearchResult<SVDBFile>> findPreProcFile(String path, boolean search_shadow) {
		List<SVDBSearchResult<SVDBFile>> ret = new ArrayList<SVDBSearchResult<SVDBFile>>();
		SVDBFile result;

		synchronized (fFileSearchOrder) {
			// Search the indexes in order
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					if ((result = index.findPreProcFile(path)) != null) {
						ret.add(new SVDBSearchResult<SVDBFile>(result, index));
					}
				}
			}
		}

		return ret;
	}
	
	public List<SVDBSearchResult<SVDBFile>> findFile(String path) {
		return findFile(path, true);
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		List<SVDBSearchResult<SVDBFile>> result = findFile(path);
		
		if (result.size() == 0) {
			return null;
		} else {
			return result.get(0).getIndex().getMarkers(path);
		}
	}
	
	public List<SVDBSearchResult<SVDBFileTree>> findFileTree(String path, boolean is_argfile) {
		List<SVDBSearchResult<SVDBFileTree>> ret = new ArrayList<SVDBSearchResult<SVDBFileTree>>();
		SVDBFileTree result;
		
		// Search the indexes in order
		synchronized (fFileSearchOrder) {
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					if ((result = index.findFileTree(path, is_argfile)) != null) {
						ret.add(new SVDBSearchResult<SVDBFileTree>(result, index));
					}
				}
			}
		}
		
		return ret;		
	}
	
	public List<SVDBSearchResult<SVDBFile>> findFile(String path, boolean search_shadow) {
		List<SVDBSearchResult<SVDBFile>> ret = new ArrayList<SVDBSearchResult<SVDBFile>>();
		SVDBFile result;
		
		// Search the indexes in order
		synchronized (fFileSearchOrder) {
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					if ((result = index.findFile(path)) != null) {
						ret.add(new SVDBSearchResult<SVDBFile>(result, index));
					}
				}
			}
		}
		
		return ret;
	}
	
	
	/**
	 * Parse content from the input stream in the context 
	 * of this index.
	 */
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor, InputStream in, String path, List<SVDBMarker> markers) {
		Tuple<SVDBFile, SVDBFile> ret = null;
		
		path = SVFileUtils.normalize(path);

		List<ISVDBIndex> result = findManagingIndex(path);
//		List<SVDBSearchResult<SVDBFile>> result = findPreProcFile(path, true);

		/*
		fLog.debug("parse(" + path + ") - results of findPreProcFile:");
		for (SVDBSearchResult<SVDBFile> r : result) {
			fLog.debug("    " + r.getIndex().getBaseLocation() + 
					" : " + r.getItem().getFilePath());
		}
		 */
		
		if (result.size() > 0) {
			// Use the parser from the associated index
			// Specify the file path in the same way that the index sees it
//			SVDBFile file = result.get(0).getItem();
			ret = result.get(0).parse(monitor, in, path, markers);
		} else {
			Exception e = null;
			try {
				throw new Exception();
			} catch (Exception ex) {
				e = ex;
			}
			fLog.error("Attempting to parse \"" + path + "\" not managed by an index", e);
		}
		
		return ret;
	}
	
	@Override
	public ISVStringPreProcessor createPreProc(String path, InputStream in,
			int limit_lineno) {
		ISVStringPreProcessor ret = null;
		
		path = SVFileUtils.normalize(path);

		List<ISVDBIndex> result = findManagingIndex(path);

		if (result.size() > 0) {
			ret = result.get(0).createPreProc(path, in, limit_lineno);
		} else {
			Exception e = null;
			try {
				throw new Exception();
			} catch (Exception ex) {
				e = ex;
			}
			fLog.error("Attempting to parse \"" + path + "\" not managed by an index", e);
		}
		
		return ret;		
	}

	public List<SVDBSearchResult<SVDBFile>> findIncParent(SVDBFile file) {
		System.out.println("[TODO] SVDBIndexCollection.findIncParent()");
		return null;
	}
	
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				List<SVDBDeclCacheItem> tmp = index.findGlobalScopeDecl(monitor, name, matcher);
				ret.addAll(tmp);
			}
		}
		Set<SVDBIndexCollection>	already_searched = new HashSet<SVDBIndexCollection>();
		findGlobalScopeDeclProjRef(ret, name, matcher, already_searched, false);
		
		/**
		 * TODO: Shadow indexes do not contribute
		for (ISVDBIndex index : fShadowIndexList) {
			List<SVDBDeclCacheItem> tmp = index.findGlobalScopeDecl(monitor, name, matcher);
			ret.addAll(tmp);
		}
		 */
		return ret;
	}
	
	public void findReferences(
			IProgressMonitor			monitor,
			ISVDBRefSearchSpec			ref_spec,
			ISVDBRefVisitor				ref_matcher) {
		
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				index.findReferences(monitor, ref_spec, ref_matcher);
			}
		}
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		StringIterableIterator ret = new StringIterableIterator();

		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				ret.addIterable(index.getFileList(new NullProgressMonitor()));
			}
		}

		Set<SVDBIndexCollection>	already_searched = new HashSet<SVDBIndexCollection>();
		getFileList(ret, already_searched, false);
	
		return ret;
	}

	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		StringIterableIterator ret = new StringIterableIterator();

		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				ret.addIterable(index.getFileList(new NullProgressMonitor(), flags));
			}
		}

		Set<SVDBIndexCollection>	already_searched = new HashSet<SVDBIndexCollection>();
		getFileList(ret, already_searched, false, flags);
	
		return ret;
	}
	
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		List<SVDBIncFileInfo> ret = new ArrayList<SVDBIncFileInfo>();

		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				List<SVDBIncFileInfo> result = index.findIncludeFiles(root, flags);
				
				for (SVDBIncFileInfo r : result) {
					if (!ret.contains(r)) {
						ret.add(r);
					}
				}
			}
		}
		
		return ret;
	}

	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		SVDBFile ret = null;
		
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				if ((ret = index.findFile(monitor, path)) != null) {
					break;
				}
			}
			if (ret != null) {
				break;
			}
		}
	
		return ret;
	}
	
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		SVDBFile ret = null;
		
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				if ((ret = index.findPreProcFile(monitor, path)) != null) {
					break;
				}
			}
			if (ret != null) {
				break;
			}
		}
	
		return ret;		
	}
	
	private void findGlobalScopeDeclProjRef(
			List<SVDBDeclCacheItem>			ret,
			String							name,
			ISVDBFindNameMatcher			matcher,
			Set<SVDBIndexCollection>		already_searched,
			boolean							search_local) {
		if (!already_searched.contains(this)) {
			already_searched.add(this);
		}
		
		if (search_local) {
			// Search for matches in the local indexes
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					List<SVDBDeclCacheItem> tmp = index.findGlobalScopeDecl(
							new NullProgressMonitor(), name, matcher);
					ret.addAll(tmp);
				}
			}
		}
		
		if (fProjectRefProvider != null) {
			for (String ref : fProjectRefs) {
				SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(ref);
				if (mgr_t != null && !already_searched.contains(mgr_t)) {
					mgr_t.findGlobalScopeDeclProjRef(ret, name, matcher, already_searched, true);
				}
			}
		}
	}
	
	private void getFileList(
			StringIterableIterator 			ret, 
			Set<SVDBIndexCollection> 		already_searched,
			boolean							search_local) {
		if (!already_searched.contains(this)) {
			already_searched.add(this);
		} else {
			return;
		}
		
		if (search_local) {
			// Search for matches in the local indexes
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					ret.addIterable(index.getFileList(new NullProgressMonitor()));
				}
			}
		}
		
		if (fProjectRefProvider != null) {
			for (String ref : fProjectRefs) {
				SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(ref);
				if (!already_searched.contains(mgr_t)) {
					already_searched.add(mgr_t);
				} else {
					continue;
				}
				if (mgr_t != null && !already_searched.contains(mgr_t)) {
					mgr_t.getFileList(ret, already_searched, search_local);
				}
			}
		}
	}

	private void getFileList(
			StringIterableIterator 			ret, 
			Set<SVDBIndexCollection> 		already_searched,
			boolean							search_local,
			int								flags) {
		if (!already_searched.contains(this)) {
			already_searched.add(this);
		} else {
			return;
		}
		
		if (search_local) {
			// Search for matches in the local indexes
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					ret.addIterable(index.getFileList(new NullProgressMonitor(), flags));
				}
			}
		}
		
		if (fProjectRefProvider != null) {
			for (String ref : fProjectRefs) {
				SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(ref);
				if (!already_searched.contains(mgr_t)) {
					already_searched.add(mgr_t);
				} else {
					continue;
				}
				if (mgr_t != null && !already_searched.contains(mgr_t)) {
					mgr_t.getFileList(ret, already_searched, search_local, flags);
				}
			}
		}
	}
	
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				List<SVDBDeclCacheItem> tmp = index.findPackageDecl(monitor, pkg_item);
				ret.addAll(tmp);
			}
		}
		
		return ret;
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				SVDBFile tmp = index.getDeclFile(monitor, item);
				if (tmp != null) {
					return tmp;
				}
			}
		}
		return null;
	}
	
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				SVDBFile tmp = index.getDeclFilePP(monitor, item);
				if (tmp != null) {
					return tmp;
				}
			}
		}
		return null;
	}
	
	public void execOp(
			IProgressMonitor 		monitor, 
			ISVDBIndexOperation 	op,
			boolean 				sync) {
		Set<ISVDBIndexOperationRunner> already_searched = new HashSet<ISVDBIndexOperationRunner>();
	
		execOp(monitor, already_searched, op, sync);
	}

	private void execOp(
			IProgressMonitor 				monitor, 
			Set<ISVDBIndexOperationRunner>	already_searched,
			ISVDBIndexOperation 			op,
			boolean 						sync) {
		synchronized (this) {
			already_searched.add(this);
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					index.execOp(monitor, op, sync);
				}
			}
			if (fProjectRefProvider != null) {
				for (String ref : fProjectRefs) {
					SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(ref);
					if (mgr_t != null && !already_searched.contains(mgr_t)) {
						mgr_t.execOp(monitor, already_searched, op, sync);
					}
				}
			}			
		}
	}
	
	private class IncludeProvider implements ISVDBIncludeFileProviderObsolete {
		ISVDBIndex					fIndex;
		List<List<ISVDBIndex>>		fSearchPath;
		
		public IncludeProvider(ISVDBIndex self) {
			fIndex = self;
			fSearchPath = new ArrayList<List<ISVDBIndex>>();
		}
		
		public void addSearchPath(List<ISVDBIndex> path) {
			fSearchPath.add(path);
		}

		public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
			SVDBSearchResult<SVDBFile> ret = null;
			
			for (List<ISVDBIndex> index_l : fSearchPath) {
				for (ISVDBIndex index : index_l) {
					if (index != fIndex && index instanceof ISVDBIncludeFileProviderObsolete) {
						ret = ((ISVDBIncludeFileProviderObsolete)index).findIncludedFile(leaf);
						
						fLog.debug("Search index \"" + index.getBaseLocation() + "\" for \"" + leaf + "\" (" + ret + ")");
						
						if (ret != null) {
							break;
						}
					}
				}
				if (ret != null) {
					break;
				}
			}
			
			if (ret == null) {
				Set<SVDBIndexCollection> searched_projects = new HashSet<SVDBIndexCollection>();
				ret = findIncludedFileProjRefs(SVDBIndexCollection.this, leaf, searched_projects);
			}
			
			return ret;
		}
		
		public SVDBSearchResult<String> findIncludedFilePath(String leaf) {
			SVDBSearchResult<String> ret = null;
			
			for (List<ISVDBIndex> index_l : fSearchPath) {
				for (ISVDBIndex index : index_l) {
					if (index != fIndex) {
						ret = index.findIncludedFilePath(leaf);
						
						fLog.debug("Search index \"" + index.getBaseLocation() + "\" for \"" + leaf + "\" (" + ret + ")");
						
						if (ret != null) {
							break;
						}
					}
				}
				if (ret != null) {
					break;
				}
			}
			
			if (ret == null) {
				// TODO:
				/*
				Set<SVDBIndexCollection> searched_projects = new HashSet<SVDBIndexCollection>();
				ret = findIncludedFileProjRefs(SVDBIndexCollection.this, leaf, searched_projects);
				 */
			}
			
			return ret;			
		}

		private SVDBSearchResult<SVDBFile> findIncludedFileProjRefs(
				SVDBIndexCollection		mgr,
				String						leaf,
				Set<SVDBIndexCollection>	searched_projects) {
			ISVDBProjectRefProvider p = mgr.getProjectRefProvider();
			SVDBSearchResult<SVDBFile> ret = null;
			
			searched_projects.add(mgr);
			
			if (mgr != SVDBIndexCollection.this) {
				// Only re-search if we're looking at another index
				for (ISVDBIndex index : mgr.getIndexList()) {
					if (index instanceof ISVDBIncludeFileProviderObsolete) {
						ret = ((ISVDBIncludeFileProviderObsolete)index).findIncludedFile(leaf);

						fLog.debug("Search index \"" + index.getBaseLocation() + 
								"\" for \"" + leaf + "\" (" + ret + ")");

						if (ret != null) {
							break;
						}
					}
				}
			}
			
			if (ret == null && p != null) {
				for (String ref : mgr.getProjectRefs()) {
					SVDBIndexCollection mgr_t = p.resolveProjectRef(ref);
					if (mgr_t != null && !searched_projects.contains(mgr_t)) {
						ret = findIncludedFileProjRefs(mgr_t, leaf, searched_projects);
						
						if (ret != null) {
							break;
						}
					}
				}
			}
			
			return ret;
		}
	};
}
