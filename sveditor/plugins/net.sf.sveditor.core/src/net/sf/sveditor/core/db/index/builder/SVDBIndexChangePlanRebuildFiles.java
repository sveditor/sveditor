package net.sf.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

public class SVDBIndexChangePlanRebuildFiles extends SVDBIndexChangePlan {
	public enum FileListType {
		Source,
		Filelist,
		Hybrid
	}

	private FileListType					fFileListType;
	private List<String>					fFileList;
	
	public SVDBIndexChangePlanRebuildFiles(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.RebuildFiles);
		fFileList = new ArrayList<String>();
		fFileListType = FileListType.Source;
	}
	
	public void addFile(String file) {
		if (!fFileList.contains(file)) {
			fFileList.add(file);
		}
	}
	
	public List<String> getFileList() {
		return fFileList;
	}
	
	public void setFileListType(FileListType type) {
		fFileListType = type;
	}

	public FileListType getFileListType() {
		return fFileListType;
	}
}
