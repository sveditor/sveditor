package net.sf.sveditor.core;

import net.sf.sveditor.core.db.SVDBFile;

public class SVDBIncludeSearch {
	
	private ISVDBIndex				fIndex;
	private boolean					fDebugEn = false;
	
	public SVDBIncludeSearch(ISVDBIndex index) {
		fIndex = index;
	}
	
	public SVDBFile findIncludedFile(String name) {
		SVDBFile ret;
		
		if ((ret = fIndex.findIncludedFile(name)) == null) {
			// Now try searching up
			ISVDBIndex index = fIndex.getSuperIndex();
			
			while (index != null) {
				if ((ret = index.findIncludedFile(name)) != null) {
					debug("        [FOUND]");
					break;
				}
				index = index.getSuperIndex();
			}
		}
		
		return ret;
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
