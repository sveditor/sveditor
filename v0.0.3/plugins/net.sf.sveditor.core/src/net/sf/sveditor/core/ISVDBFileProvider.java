package net.sf.sveditor.core;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public interface ISVDBFileProvider {
	
	void add_path(String path);
	
	SVDBFile getFile(String path);

}
