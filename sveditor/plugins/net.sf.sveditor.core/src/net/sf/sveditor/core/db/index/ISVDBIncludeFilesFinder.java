package net.sf.sveditor.core.db.index;

import java.util.List;

public interface ISVDBIncludeFilesFinder {

	int FIND_INC_SV_FILES      = 0x01;
	int FIND_INC_ARG_FILES     = 0x02;
	int FIND_INC_ALL_FILES     = 0x04;

	/**
	 * findIncludeFiles()
	 * 
	 * Locates include paths 
	 */
	List<SVDBIncFileInfo> findIncludeFiles(String root, int flags);
}
