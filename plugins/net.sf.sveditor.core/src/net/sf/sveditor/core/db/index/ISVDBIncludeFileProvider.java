package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBIncludeFileProvider {

	/**
	 * Locates a file with the following leaf. If the file cannot be
	 * found, returns 'null'
	 * 
	 * @param suffix
	 * @return
	 */
	SVDBFile findIncludedFile(String leaf);
	

}
