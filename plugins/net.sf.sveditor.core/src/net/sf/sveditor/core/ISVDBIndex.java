package net.sf.sveditor.core;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBIndex {

	void dispose();
	
	File getBaseLocation();
	
	List<SVDBFile> getFileList();
	
	// TODO: add support for change listeners ???
}
