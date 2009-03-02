package net.sf.sveditor.core;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBIndexChangeListener {
	
	int FILE_ADDED   = 1;
	int FILE_REMOVED = 2;
	int FILE_CHANGED = 3;
	
	
	void index_changed(int reason, SVDBFile file);

}
