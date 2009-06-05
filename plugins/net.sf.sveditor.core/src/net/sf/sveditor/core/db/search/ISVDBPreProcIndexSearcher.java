package net.sf.sveditor.core.db.search;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBPreProcIndexSearcher {
	
	/**
	 * Search the pre-processor view of files looking for the file 
	 * with the specified path
	 * 
	 * @param path
	 * @return
	 */
	List<SVDBSearchResult<SVDBFile>> findPreProcFile(String path);
	
	List<SVDBSearchResult<SVDBFile>> findIncParent(SVDBFile file);

}
