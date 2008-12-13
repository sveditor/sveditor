package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVDBProjectDataFileProvider implements ISVDBFileProvider {
	
	private SVDBProjectData			fProjectData;
	
	public SVDBProjectDataFileProvider(SVDBProjectData proj_data) {
		fProjectData = proj_data;
	}
	
	public void add_path(String path) {
		
	}

	
	public SVDBFile getFile(String path) {
		SVDBFile ret = null;
		SVDBWorkspaceFileManager mgr = fProjectData.getFileCache();
		
		System.out.println("getFile(\"" + path + "\")");
		
		for (SVDBPath p : fProjectData.getProjectFileWrapper().getIncludePaths()) {
			System.out.println("path: " + p.getPath());
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
	}

}
