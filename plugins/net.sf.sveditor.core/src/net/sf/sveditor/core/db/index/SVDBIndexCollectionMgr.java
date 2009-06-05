package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.search.ISVDBPreProcIndexSearcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

public class SVDBIndexCollectionMgr implements ISVDBPreProcIndexSearcher, ISVDBIndexIterator {
	private String							fProject;
	private List<ISVDBIndex>				fSourceCollectionList;
	private List<ISVDBIndex>				fIncludePathList;
	private List<ISVDBIndex>				fLibraryPathList;
	private List<ISVDBIndex>				fPluginLibraryList;
	private List<List<ISVDBIndex>>			fFileSearchOrder;
	private Map<String, ISVDBIndex>			fShadowIndexes;

	
	public SVDBIndexCollectionMgr(String project) {
		fProject 				= project;
		fSourceCollectionList 	= new ArrayList<ISVDBIndex>();
		fIncludePathList 		= new ArrayList<ISVDBIndex>();
		fLibraryPathList 		= new ArrayList<ISVDBIndex>();
		fPluginLibraryList 		= new ArrayList<ISVDBIndex>();
		fShadowIndexes			= new HashMap<String, ISVDBIndex>();
		
		fFileSearchOrder		= new ArrayList<List<ISVDBIndex>>();
		fFileSearchOrder.add(fSourceCollectionList);
		fFileSearchOrder.add(fIncludePathList);
		fFileSearchOrder.add(fLibraryPathList);
		fFileSearchOrder.add(fPluginLibraryList);
	}
	
	public void clear() {
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
	
	@Override
	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		SVDBIndexCollectionItemIterator ret = new SVDBIndexCollectionItemIterator();
		
		for (List<ISVDBIndex> i_l : fFileSearchOrder) {
			for (ISVDBIndex index : i_l){
				ret.addIndex(index);
			}
		}
		
		return ret;
	}

	public void addSourceCollection(ISVDBIndex index) {
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		fSourceCollectionList.add(index);
	}
	
	public void addShadowIndex(String dir, ISVDBIndex index) {
		IncludeProvider p = new IncludeProvider(index);
		p.addSearchPath(fSourceCollectionList);
		p.addSearchPath(fIncludePathList);
		p.addSearchPath(fLibraryPathList);
		p.addSearchPath(fPluginLibraryList);
		index.setIncludeFileProvider(p);
		
		fShadowIndexes.put(dir, index);
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
	
	public List<SVDBSearchResult<SVDBFile>> findPreProcFile(String path) {
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
			for (ISVDBIndex index : fShadowIndexes.values()) {
				if ((result = index.findPreProcFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}
		
		/*
		if (ret.size() == 0) {
			System.out.println("Failed to find pre-proc file \"" + path + "\"");
			System.out.println("    Searched the following files");
			for (List<ISVDBIndex> index_l : fFileSearchOrder) {
				for (ISVDBIndex index : index_l) {
					System.out.println("        Index: " + index.getClass().getName());
					for (String file : index.getPreProcFileMap().keySet()) {
						System.out.println("            " + file);
						
					}
				}
			}
			
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		 */
		
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
			for (ISVDBIndex index : fShadowIndexes.values()) {
				if ((result = index.findFile(path)) != null) {
					ret.add(new SVDBSearchResult<SVDBFile>(result, index));
				}
			}
		}
		
		return ret;
	}
	
	public SVDBFile parse(InputStream in, String path) {
		SVDBFile ret = null;
		
		List<SVDBSearchResult<SVDBFile>> result = findPreProcFile(path);
		
		if (result.size() > 0) {
			// Use the parser from the associated index
			ret = result.get(0).getIndex().parse(in, path);
		} else {
			// Create a shadow index using the current directory
			String dir = new File(path).getParent();
			
			if (!fShadowIndexes.containsKey(dir)) {
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
			
			ret = fShadowIndexes.get(dir).parse(in, path);
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

		public SVDBFile findIncludedFile(String leaf) {
			SVDBFile ret;
			
			if ((ret = findIncludedFile(fIndex, leaf)) != null) {
				System.out.println("findIncludedFile \"" + leaf + "\" in " +
						"current index \"" + fIndex.getBaseLocation() + "\"");
				return ret;
			}
			
			for (List<ISVDBIndex> index_l : fSearchPath) {
				for (ISVDBIndex index : index_l) {
					if (index != fIndex) {
						if ((ret = findIncludedFile(index, leaf)) != null) {
							System.out.println("findIncludedFile \"" + leaf + "\" in " +
									"index \"" + index.getBaseLocation() + "\"");
							return ret;
						}
					}
				}
			}
			
			return ret;
		}
		
		private SVDBFile findIncludedFile(ISVDBIndex index, String leaf) {
			Map<String, SVDBFile> pp_map = index.getPreProcFileMap();
			
			for (String f : pp_map.keySet()) {
				if (f.endsWith(leaf)) {
					return pp_map.get(f);
				}
			}
			
			return null;
		}
	};
}
