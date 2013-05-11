package net.sf.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

public class SVDBIndexChangePlanRebuildFiles extends SVDBIndexChangePlan {
	private List<String>					fFileList;
	
	public SVDBIndexChangePlanRebuildFiles(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.RebuildFiles);
		fFileList = new ArrayList<String>();
	}
	
	public void addFile(String file) {
		if (!fFileList.contains(file)) {
			fFileList.add(file);
		}
	}
	
	public List<String> getFileList() {
		return fFileList;
	}

}
