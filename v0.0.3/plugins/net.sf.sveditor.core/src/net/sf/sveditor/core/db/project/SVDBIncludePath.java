package net.sf.sveditor.core.db.project;

import java.io.File;

public class SVDBIncludePath {
	
	private boolean					fIsWSRelPath;
	private String					fPath;
	
	public SVDBIncludePath(String path, boolean is_wsrel_path) {
		fIsWSRelPath = is_wsrel_path;
		fPath = path;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public boolean isWSRelPath() {
		return fIsWSRelPath;
	}

}
