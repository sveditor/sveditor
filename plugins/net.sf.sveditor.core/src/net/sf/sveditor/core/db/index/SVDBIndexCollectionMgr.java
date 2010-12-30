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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.search.ISVDBPreProcIndexSearcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
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
	
	public ISVDBItemIterator getItemIterator() {
		SVDBIndexCollectionItemIterator ret = new SVDBIndexCollectionItemIterator();
		
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
	
	public SVDBFile parse(InputStream in, String path) {
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
			ret = result.get(0).getIndex().parse(in, path);
		} else {
			// Create a shadow index using the current directory
			String dir = SVFileUtils.getPathParent(path);
			
			if (!fShadowIndexMap.containsKey(dir)) {
				ISVDBIndex index = null;
				
				if (fProject != null) {
					SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
					index = rgy.findCreateIndex(
						fProject, dir, SVDBSourceCollectionIndexFactory.TYPE,
						null);
				} else {
					System.out.println("[TODO] create shadow index for " +
							"non-project file");
				}
				
				addShadowIndex(dir, index);
			}
			
			ret = fShadowIndexMap.get(dir).parse(in, path);
		}
		
		return ret;
	}
	
	public List<SVDBSearchResult<SVDBFile>> findIncParent(SVDBFile file) {
		System.out.println("[TODO] SVDBIndexCollection.findIncParent()");
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
