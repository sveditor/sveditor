package net.sf.sveditor.core;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVDBProjectDataFileProvider implements ISVDBFileProvider {
	
	private SVDBProjectData			fProjectData;
	
	public SVDBProjectDataFileProvider(SVDBProjectData proj_data) {
		fProjectData = proj_data;
	}
	
	public void add_path(String path) {
		
	}

	public SVDBFile getFile(String path) {
		/*
		SVDBFile ret = null;
		SVDBWorkspaceFileManager mgr = fProjectData.getFileCache();
		
		for (SVDBPath p : fProjectData.getProjectFileWrapper().getIncludePaths()) {
			if (p.isWSRelPath()) {
				System.out.println("[TODO] WSRelPath()");
			} else {
				File f = new File(p.getPath(), path);
				
				if (f.isFile()) {
					ret = mgr.getFile(f, this);
				}
			}
			
			if (ret != null) {
				break;
			}
		}
		return ret;
	 */
		System.out.println("[FIXME] SVDBProjectDataFile.getFile()");
		return null;
	}
	
}
