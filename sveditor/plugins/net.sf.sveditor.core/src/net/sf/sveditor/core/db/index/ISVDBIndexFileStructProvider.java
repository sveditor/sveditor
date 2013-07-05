package net.sf.sveditor.core.db.index;

import java.util.List;

public interface ISVDBIndexFileStructProvider {

	/**
	 * @param path
	 * @return
	 */
	List<SVDBFilePath> getFilePath(String path);
	

}
