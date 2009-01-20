package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class SVDBFileTree {
	
	File					fFilePath;
	SVDBFile				fSVDBFile;
	List<SVDBFileTree>      fIncludedFiles   = new ArrayList<SVDBFileTree>();
	List<SVDBFileTree>		fIncludedByFiles = new ArrayList<SVDBFileTree>();

	public SVDBFileTree(File path) {
		fFilePath = path;
	}

	public SVDBFileTree(SVDBFile file) {
		fFilePath = file.getFilePath();
		fSVDBFile = file;
	}
	
	
	public File getFilePath() {
		return fFilePath;
	}
	
	public void setFileName(File path) {
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
