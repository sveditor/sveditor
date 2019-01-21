package net.sf.sveditor.core.db.index.auto;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;

public class SVAutoIndexBuildData {
	
	private ISVDBFileSystemProvider			fFileSystemProvider;
	private ISVDBIndexCache					fCache;
	private SVAutoIndexCacheData			fCacheData;
	private Set<String>						fFailedSearches;
	private List<String>					fIncDirs;
	
	public SVAutoIndexBuildData(ISVDBIndexCache cache, String base_location) {
		fCache = cache;
		fCacheData = new SVAutoIndexCacheData(base_location);
		
		fCache.init(new NullProgressMonitor(), fCacheData, base_location);
		
		fFailedSearches = new HashSet<String>();
		fIncDirs = new ArrayList<String>();
	}
	
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}
	
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
	}
	
	public ISVPreProcIncFileProvider getIncFileProvider() {
		return fIncFileProvider;
	}
	
	public void setIncDirs(List<String> inc_dirs) {
		fIncDirs.clear();
		fIncDirs.addAll(inc_dirs);
	}
	
	public void addIncDir(String inc_dir) {
		fIncDirs.add(inc_dir);
	}

	/**
	 * Implementation of the include-file finder
	 */
	private ISVPreProcIncFileProvider fIncFileProvider = new ISVPreProcIncFileProvider() {
		
		@Override
		public Tuple<String, InputStream> findIncFile(String incfile) {
			Tuple<String, InputStream> ret = null;
			
			// TODO: We'd like to look close to the source file, but
			// we don't have that info
			
			for (String inc : fIncDirs) {
				String fullpath = inc + "/" + incfile;
				
				if (fFileSystemProvider.fileExists(fullpath)) {
					ret = new Tuple<String, InputStream>(fullpath, 
							fFileSystemProvider.openStream(fullpath));
					break;
				}
			}

			return ret;
		}
		
		@Override
		public Tuple<String, List<SVDBFileTreeMacroList>> findCachedIncFile(String incfile) {
			// KISS for now
			return null;
		}
		
		@Override
		public void addCachedIncFile(String incfile, String rootfile) {
			// KISS for now
		}
	};

}
