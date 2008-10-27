package net.sf.sveditor.core.db.project;

import org.eclipse.core.runtime.IPath;

import net.sf.sveditor.core.SVDBFileManager;
import net.sf.sveditor.core.SVProjectFileWrapper;

public class SVDBProjectData {
	private IPath								fSVProjFilePath;
	private SVProjectFileWrapper				fFileWrapper;
	private SVDBFileManager						fFileCache;
	
	public SVDBProjectData(
			SVProjectFileWrapper 	wrapper,
			IPath					projfile_path) {
		fSVProjFilePath = projfile_path;
		fFileWrapper = wrapper;
		fFileCache   = new SVDBFileManager();
	}
	
	public SVDBFileManager getFileCache() {
		return fFileCache;
	}
	
	public SVProjectFileWrapper getProjectFileWrapper() {
		 return fFileWrapper;
	}
	
	public void setProjectFileWrapper(SVProjectFileWrapper w) {
		System.out.println("TODO: setProjectFileWrapper()");
	}
	
	public void refreshProjectData() {
		System.out.println("[TODO] refreshProjectData()");
	}

}
