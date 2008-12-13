package net.sf.sveditor.core.db.project;


public class SVDBPath {
	
	private boolean					fIsWSRelPath;
	private String					fPath;
	
	public SVDBPath(String path, boolean is_wsrel_path) {
		fIsWSRelPath = is_wsrel_path;
		fPath = path;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public void setPath(String path) {
		fPath = path;
	}
	
	public boolean isWSRelPath() {
		return fIsWSRelPath;
	}

}
