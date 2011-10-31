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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.ISVDBPreProcIndexSearcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBIndexCollectionMgr implements ISVDBPreProcIndexSearcher, ISVDBIndexIterator {
	private String							fProject;
	private List<ISVDBIndex>				fSourceCollectionList;
	private List<ISVDBIndex>				fIncludePathList;
	private List<ISVDBIndex>				fLibraryPathList;
	private List<ISVDBIndex>				fPluginLibraryList;
	private List<ISVDBIndex>				fShadowIndexList;
	private List<List<ISVDBIndex>>			fFileSearchOrder;
	private Map<String, ISVDBIndex>			fShadowIndexMap;
	private LogHandle						fLog;
	
	public SVDBIndexCollectionMgr(String project) {
		fProject 				= project;
		fSourceCollectionList 	= new ArrayList<ISVDBIndex>();
		fIncludePathList 		= new ArrayList<ISVDBIndex>();
		fLibraryPathList 		= new ArrayList<ISVDBIndex>();
		fPluginLibraryList 		= new ArrayList<ISVDBIndex>();
		fShadowIndexList		= new ArrayList<ISVDBIndex>();

		fShadowIndexMap			= new HashMap<String, ISVDBIndex>();
		
		fFileSearchOrder		= new ArrayList<List<ISVDBIndex>>();
		fFileSearchOrder.add(fLibraryPathList);
		fFileSearchOrder.add(fSourceCollectionList);
		fFileSearchOrder.add(fIncludePathList);
		fFileSearchOrder.add(fPluginLibraryList);
		
		fLog = LogFactory.getLogHandle("IndexCollectionMgr");
	}
	
	public String getProject() {
		return fProject;
	}
	
	public void rebuildIndex() {
		for (ISVDBIndex i : getIndexList()) {
			i.rebuildIndex();
		}
		for (ISVDBIndex i : fShadowIndexList) {
			i.rebuildIndex();
		}
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
	}
	
	public List<ISVDBIndex> getIndexList() {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			ret.addAll(i_l);
		}
		
		return ret;
	}
	
	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		SVDBIndexCollectionItemIterator ret = new SVDBIndexCollectionItemIterator(monitor);
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			for (ISVDBIndex index : i_l){
				ret.addIndex(index);
			}
		}
		
		// Finally, add the shadow indexes
		for (ISVDBIndex index : fShadowIndexList) {
			ret.addIndex(index);
		}
		
		return ret;
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
	}
	
	public List<ISVDBIndex> getSourceCollectionList() {
		return fSourceCollectionList;
	}
	
	public void addShadowIndex(String dir, ISVDBIndex index) {
		fLog.debug("addShadowIndex: " + dir + "(" + index.getBaseLocation() + ")");
		
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		
		fShadowIndexList.add(index);
		fShadowIndexMap.put(dir, index);
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
	}
	
	
	public List<SVDBSearchResult<SVDBFile>> findPreProcFile(String path, boolean search_shadow) {
		List<SVDBSearchResult<SVDBFile>> ret = new ArrayList<SVDBSearchResult<SVDBFile>>();
		SVDBFile result;
		
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				if ((result = index.findPreProcFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}

		if (ret.size() == 0) {
			for (ISVDBIndex index : fShadowIndexMap.values()) {
				if ((result = index.findPreProcFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}
		
		return ret;
	}
	
	public List<SVDBSearchResult<SVDBFile>> findFile(String path) {
		List<SVDBSearchResult<SVDBFile>> ret = new ArrayList<SVDBSearchResult<SVDBFile>>();
		SVDBFile result;
		
		// Search the indexes in order
		for (List<ISVDBIndex> index_l : fFileSearchOrder) {
			for (ISVDBIndex index : index_l) {
				if ((result = index.findFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}
		
		if (ret.size() == 0) {
			for (ISVDBIndex index : fShadowIndexMap.values()) {
				if ((result = index.findFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}
		
		return ret;
	}
	
	/**
	 * Parse content from the input stream in the context 
	 * of this index.
	 */
	public SVDBFile parse(IProgressMonitor monitor, InputStream in, String path, List<SVDBMarker> markers) {
		SVDBFile ret = null;
		
		path = SVFileUtils.normalize(path);
		
		List<SVDBSearchResult<SVDBFile>> result = findPreProcFile(path, true);
		
		fLog.debug("parse(" + path + ") - results of findPreProcFile:");
		for (SVDBSearchResult<SVDBFile> r : result) {
			fLog.debug("    " + r.getIndex().getBaseLocation() + 
					" : " + r.getItem().getFilePath());
		}
		
		if (result.size() > 0) {
			// Use the parser from the associated index
			ret = result.get(0).getIndex().parse(monitor, in, path, markers);
		} else {
			// Create a shadow index using the current directory
			String dir = SVFileUtils.getPathParent(path);
			
			if (!fShadowIndexMap.containsKey(dir)) {
				ISVDBIndex index = null;
				
				if (fProject != null) {
					SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
					SVFileSet fs = new SVFileSet(dir);
					
					// Remove the depth-searching portion from all patterns
					String dflt_include = SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes();
					dflt_include = dflt_include.replace("**/", "");
					String dflt_exclude = SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes();
					dflt_exclude = dflt_exclude.replace("**/", "");
					fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(dflt_include));
					fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(dflt_exclude));
					
					Map<String, Object> config = new HashMap<String, Object>();
					config.put(SVDBSourceCollectionIndexFactory.FILESET, fs);
					
					index = rgy.findCreateIndex(new NullProgressMonitor(),
						fProject, dir, SVDBSourceCollectionIndexFactory.TYPE, config);
				} else {
					System.out.println("[TODO] create shadow index for " +
							"non-project file");
				}
				
				addShadowIndex(dir, index);
			}
			
			ret = fShadowIndexMap.get(dir).parse(monitor, in, path, markers);
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
		for (ISVDBIndex index : fShadowIndexList) {
			List<SVDBDeclCacheItem> tmp = index.findGlobalScopeDecl(monitor, name, matcher);
			ret.addAll(tmp);
		}
		return ret;
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
		for (ISVDBIndex index : fShadowIndexList) {
			List<SVDBDeclCacheItem> tmp = index.findPackageDecl(monitor, pkg_item);
			ret.addAll(tmp);
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



	private class IncludeProvider implements ISVDBIncludeFileProvider {
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
					if (index != fIndex) {
						ret = index.findIncludedFile(leaf);
						
						fLog.debug("Search index \"" + index.getBaseLocation() + "\" for \"" + leaf + "\" (" + ret + ")");
						
						if (ret != null) {
							return ret;
						}
					}
				}
			}
			
			return ret;
		}
	};
}
