package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

/**
 * Implements an include files finder for a specific directory
 * 
 * @author ballance
 *
 */
public class SVDBShadowIncludeFilesFinder implements ISVDBIncludeFilesFinder {
	private List<String>					fDirList;
	
	public SVDBShadowIncludeFilesFinder(String dir) {
		fDirList = new ArrayList<String>();
		fDirList.add(dir);
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		return SVDBFindIncFileUtils.findIncludeFiles(
				null,
				new SVDBWSFileSystemProvider(),
				fDirList,
				root, flags);		
	}

}
