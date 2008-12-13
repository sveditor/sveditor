package net.sf.sveditor.core;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;

public class SVDBIndexList implements ISVDBIndex {
	
	private List<ISVDBIndex>				fIndexList;
	private File							fProjectDir;
	
	public SVDBIndexList(File project_dir) {
		fIndexList = new ArrayList<ISVDBIndex>();
		fProjectDir = project_dir;
	}

	public void dispose() {
		for (ISVDBIndex idx : fIndexList) {
			idx.dispose();
		}
	}

	public File getBaseLocation() {
		return fProjectDir; 
	}
	
	public void addIndex(ISVDBIndex idx) {
		// TODO: signal change event?
		fIndexList.add(idx);
	}

	public List<SVDBFile> getFileList() {
		List<SVDBFile> ret = new ArrayList<SVDBFile>();
		
		for (ISVDBIndex idx : fIndexList) {
			ret.addAll(idx.getFileList());
		}
		
		return ret;
	}
}
