package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBFileTree {
	
	String					fFilePath;
	SVDBFile				fSVDBFile;
	List<SVDBFileTree>      fIncludedFiles   = new ArrayList<SVDBFileTree>();
	List<SVDBFileTree>		fIncludedByFiles = new ArrayList<SVDBFileTree>();

	public SVDBFileTree(String path) {
		fFilePath = path;
	}

	public SVDBFileTree(SVDBFile file) {
		fFilePath = file.getFilePath().getAbsolutePath();
		fSVDBFile = file;
	}
	
	
	public String getFilePath() {
		return fFilePath;
	}
	
	public void setFileName(String path) {
		fFilePath = path;
	}
	
	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public void setSVDBFile(SVDBFile file) {
		fSVDBFile = file;
	}
	
	public List<SVDBFileTree> getIncludedFiles() {
		return fIncludedFiles;
	}
	
	public List<SVDBFileTree> getIncludedByFiles() {
		return fIncludedByFiles;
	}

	public boolean equals(Object other) {
		if (other != null && other instanceof SVDBFileTree) {
			SVDBFileTree other_t = (SVDBFileTree)other;
			boolean ret = true;
			
			if (other_t.fFilePath == null || fFilePath == null) {
				ret &= (other_t.fFilePath == fFilePath);
			} else {
				ret &= (other_t.fFilePath.equals(fFilePath));
			}
			
			return ret;
		} else {
			return false;
		}
	}

}
