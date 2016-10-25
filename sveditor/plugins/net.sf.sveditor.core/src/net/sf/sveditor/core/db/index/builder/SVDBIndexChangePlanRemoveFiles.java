package net.sf.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

public class SVDBIndexChangePlanRemoveFiles extends SVDBIndexChangePlan {
	private List<String>				fFiles;
	
	public SVDBIndexChangePlanRemoveFiles(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.RemoveFiles);
		fFiles = new ArrayList<String>();
	}
	
	public void addFile(String path) {
		fFiles.add(path);
	}
	
	public List<String> getFiles() {
		return fFiles;
	}

}
