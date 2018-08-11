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


package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringIterableIterator;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBVisitor;
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

public class SVDBIndexCollection implements ISVDBPreProcIndexSearcher, ISVDBIndexIterator,
		ISVDBIndexOperationRunner, ISVDBIndexParse, ILogLevel {
	private SVDBIndexCollectionMgr					fMgr;
	private String									fProject;
	private List<ISVDBIndex>						fBuiltinIndex;
	private List<ISVDBIndex>						fSourceCollectionList;
	private List<ISVDBIndex>						fIncludePathList;
	private List<ISVDBIndex>						fArgFilePathList;
	private List<ISVDBIndex>						fPluginLibraryList;
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
		fArgFilePathList 		= new ArrayList<ISVDBIndex>();
		fPluginLibraryList 		= new ArrayList<ISVDBIndex>();
		fProjectRefs			= new HashSet<String>();

		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		
		fLog = LogFactory.getLogHandle("IndexCollectionMgr");
		
		if (fMgr != null) {
			fMgr.addIndexCollection(this);
		}
	}
	
	public void loadIndex(IProgressMonitor monitor) {
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		subMonitor.beginTask("loadIndex",
				fSourceCollectionList.size() + 
				fIncludePathList.size() + 
				fArgFilePathList.size() + 
				fPluginLibraryList.size());
		
		synchronized (fSourceCollectionList) {
			for (ISVDBIndex index : fSourceCollectionList) {
				index.loadIndex(subMonitor.newChild(1));
			}
		}
		
		synchronized (fIncludePathList) {
			for (ISVDBIndex index : fIncludePathList) {
				index.loadIndex(subMonitor.newChild(1));
			}
		}
		
		synchronized (fArgFilePathList) {
			for (ISVDBIndex index : fArgFilePathList) {
				index.loadIndex(subMonitor.newChild(1));
			}
		}
		
		synchronized (fPluginLibraryList) {
			for (ISVDBIndex index : fPluginLibraryList) {
				index.loadIndex(subMonitor.newChild(1));
			}
		}
		
		subMonitor.done();
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
		
		synchronized (fArgFilePathList) {
			for (ISVDBIndex index : fArgFilePathList) {
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
		
		synchronized (fArgFilePathList) {
			for (ISVDBIndex index : fArgFilePathList) {
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
		
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			for (ISVDBIndex index : index_l) {
				index.addChangeListener(l);
			}
		}
	}
	
	public void removeIndexChangeListener(ISVDBIndexChangeListener l) {
		fIndexChangeListeners.remove(l);

		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		/*
		for (ISVDBIndex i : getIndexList()) {
			i.rebuildIndex(monitor);
		}
		 */
		subMonitor.beginTask("Rebuild Indexes", 1000*getIndexList().size());
		for (ISVDBIndex i : getIndexList()) {
			i.execIndexChangePlan(subMonitor.newChild(1000),
					new SVDBIndexChangePlanRebuild(i));
		}
		subMonitor.done();
	}
	
	public void clear() {
		fLog.debug("clear");
		fSourceCollectionList.clear();
		fIncludePathList.clear();
		fArgFilePathList.clear();
		fPluginLibraryList.clear();
		fProjectRefs.clear();
	}
	
	public List<ISVDBIndex> getIndexList() {
		return getIndexList(false);
	}
	
	public List<ISVDBIndex> getIndexList(boolean include_builtin) {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		for (List<ISVDBIndex> i_l : getFileSearchOrder()) {
			// Don't consider the builtin index to be part of this collection
			if (i_l != fBuiltinIndex || include_builtin) {
				ret.addAll(i_l);
			}
		}
		
		return ret;
	}

	public List<SVDBFilePath> getFilePath(String path) {
		List<SVDBFilePath> ret = new ArrayList<SVDBFilePath>();
		
		for (List<ISVDBIndex> i_l : getFileSearchOrder()) {
			for (ISVDBIndex index : i_l) {
				List<SVDBFilePath> p = index.getFilePath(path);
				ret.addAll(p);
			}
		}
		
		return ret;
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
		
//		IncludeProvider p = new IncludeProvider(index);
//		p.addSearchPath(fSourceCollectionList);
//		p.addSearchPath(fIncludePathList);
//		p.addSearchPath(fLibraryPathList);
//		p.addSearchPath(fPluginLibraryList);
//		index.setIncludeFileProvider(p);
		fSourceCollectionList.add(index);
		
		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> getSourceCollectionList() {
		return fSourceCollectionList;
	}
	
	public void addIncludePath(ISVDBIndex index) {
//		IncludeProvider p = new IncludeProvider(index);
//		p.addSearchPath(fIncludePathList);
//		p.addSearchPath(fLibraryPathList);
//		p.addSearchPath(fSourceCollectionList);
//		p.addSearchPath(fPluginLibraryList);
//		index.setIncludeFileProvider(p);
		fIncludePathList.add(index);
	}
	
	public void addArgFilePath(ISVDBIndex index) {
		fArgFilePathList.add(index);
		
		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> getArgFilePathList() {
		return fArgFilePathList;
	}
	
	public List<ISVDBIndex> getPluginPathList() {
		return fPluginLibraryList;
	}
	
	public void addPluginLibrary(ISVDBIndex index) {
		fPluginLibraryList.add(index);

		for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
			index.addChangeListener(l);
		}
	}
	
	public List<ISVDBIndex> findManagingIndex(String path) {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		synchronized (getFileSearchOrder()) {
			// Search the indexes in order
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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

		synchronized (getFileSearchOrder()) {
			// Search the indexes in order
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		synchronized (getFileSearchOrder()) {
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		synchronized (getFileSearchOrder()) {
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		
		if (result.size() > 0) {
			// Use the parser from the associated index
			// Specify the file path in the same way that the index sees it
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
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				index.findReferences(loopMonitor.newChild(1), ref_spec, ref_matcher);
			}
		}
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		StringIterableIterator ret = new StringIterableIterator();

		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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

		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			for (ISVDBIndex index : index_l) {
				ret.addIterable(index.getFileList(new NullProgressMonitor(), flags));
			}
		}

		Set<SVDBIndexCollection>	already_searched = new HashSet<SVDBIndexCollection>();
		getFileList(ret, already_searched, true, flags);
	
		return ret;
	}
	
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		List<SVDBIncFileInfo> ret = new ArrayList<SVDBIncFileInfo>();

		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				if ((ret = index.findFile(loopMonitor.newChild(1), path)) != null) {
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
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				if ((ret = index.findPreProcFile(loopMonitor.newChild(1), path)) != null) {
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
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
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
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				List<SVDBDeclCacheItem> tmp = index.findPackageDecl(loopMonitor.newChild(1), pkg_item);
				ret.addAll(tmp);
			}
		}
		
		return ret;
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				SVDBFile tmp = index.getDeclFile(loopMonitor.newChild(1), item);
				if (tmp != null) {
					return tmp;
				}
			}
		}
		return null;
	}
	
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		SubMonitor subMonitor = SubMonitor.convert(monitor, getFileSearchOrder().size());
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			SubMonitor loopMonitor = subMonitor.newChild(1);
			loopMonitor.setWorkRemaining(index_l.size());
			for (ISVDBIndex index : index_l) {
				SVDBFile tmp = index.getDeclFilePP(loopMonitor.newChild(1), item);
				if (tmp != null) {
					return tmp;
				}
			}
		}
		return null;
	}
	
	public String mapFileIdToPath(int id) {
		// Error: must not be called
		return null;
	}
	
	public void execOp(
			IProgressMonitor 		monitor, 
			ISVDBIndexOperation 	op,
			boolean 				sync) {
		Set<ISVDBIndexOperationRunner> already_searched = new HashSet<ISVDBIndexOperationRunner>();
	
		execOp(monitor, already_searched, op, sync);
	}
	

	@Override
	public void accept(ISVDBVisitor v) {
		for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
			for (ISVDBIndex index : index_l) {
				index.accept(v);
			}
		}
	}

	private void execOp(
			IProgressMonitor 				monitor, 
			Set<ISVDBIndexOperationRunner>	already_searched,
			ISVDBIndexOperation 			op,
			boolean 						sync) {
		synchronized (this) {
			SubMonitor subMonitor = SubMonitor.convert(monitor);
			int workRemaining = getFileSearchOrder().size();
			if (fProjectRefProvider != null)
				workRemaining += fProjectRefs.size();
			subMonitor.setWorkRemaining(workRemaining);
			
			already_searched.add(this);
			for (List<ISVDBIndex> index_l : getFileSearchOrder()) {
				for (ISVDBIndex index : index_l) {
					index.execOp(subMonitor.newChild(1), op, sync);
				}
			}
			if (fProjectRefProvider != null) {
				for (String ref : fProjectRefs) {
					SVDBIndexCollection mgr_t = fProjectRefProvider.resolveProjectRef(ref);
					if (mgr_t != null && !already_searched.contains(mgr_t)) {
						mgr_t.execOp(subMonitor.newChild(1), already_searched, op, sync);
					}
				}
			}			
		}
	}

	List<List<ISVDBIndex>> getFileSearchOrder() {
		List<List<ISVDBIndex>> ret = new ArrayList<List<ISVDBIndex>>();
		if (fBuiltinIndex == null) {
			fBuiltinIndex = new ArrayList<ISVDBIndex>();
			fBuiltinIndex.add(SVCorePlugin.getDefault().getBuiltinLib());
		}
		ret.add(fBuiltinIndex);
		ret.add(fArgFilePathList);
		ret.add(fSourceCollectionList);
		ret.add(fIncludePathList);
		ret.add(fPluginLibraryList);
	
		return ret;
	}
}
