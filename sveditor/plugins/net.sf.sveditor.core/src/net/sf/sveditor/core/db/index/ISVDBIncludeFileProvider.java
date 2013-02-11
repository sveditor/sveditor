package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.search.SVDBSearchResult;

public interface ISVDBIncludeFileProvider {

	/**
	 * @param leaf
	 * @return
	 */
	SVDBSearchResult<String> findIncludedFilePath(String leaf);
}
