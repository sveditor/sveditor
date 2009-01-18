package net.sf.sveditor.core;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;

public interface ISVDBFileProvider {
	
	void add_path(String path);
	
	SVDBFile getFile(String path);
	
	SVDBFileTree getFileTree(String path);

}
