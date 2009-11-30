package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

public interface ISVDBIncludeFileProvider {

	/**
	 * Locates a file with the following leaf. If the file cannot be
	 * found, returns 'null'
	 * 
	 * @param suffix
	 * @return
	 */
	SVDBSearchResult<SVDBFile> findIncludedFile(String leaf);
	

}
