package net.sf.sveditor.core;

import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVDBProjectDataFileProvider implements ISVDBFileProvider {
	
	private SVDBProjectData			fProjectData;
	
	public SVDBProjectDataFileProvider(SVDBProjectData proj_data) {
		fProjectData = proj_data;
	}
	
	public void add_path(String path) {
		
	}
	
}
