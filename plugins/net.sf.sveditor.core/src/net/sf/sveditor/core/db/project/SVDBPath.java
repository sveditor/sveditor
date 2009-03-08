package net.sf.sveditor.core.db.project;


public class SVDBPath {
	
	private boolean					fIsWSRelPath;
	private String					fPath;
	private boolean					fPhantom;
	
	public SVDBPath(String path, boolean is_wsrel_path, boolean is_phantom) {
		fIsWSRelPath = is_wsrel_path;
		fPath        = path;
		fPhantom     = is_phantom;
	}

	/**
	 * Indicates whether this path entry belongs in the .svproject file
	 * @return
	 */
	public boolean getIsPhantom() {
		return fPhantom;
	}
	
	public void setIsPhantom(boolean is_phantom) {
		fPhantom = is_phantom;
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
	
	public boolean equals(Object other) {
		if (other instanceof SVDBPath) {
			SVDBPath other_p = (SVDBPath)other;
			
			if (other_p.fIsWSRelPath == fIsWSRelPath &&
					other_p.fPath.equals(fPath)) {
				return true;
			}
		}
		return false;
	}
}
