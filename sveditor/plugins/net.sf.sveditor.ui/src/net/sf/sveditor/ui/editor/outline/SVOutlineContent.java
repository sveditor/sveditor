package net.sf.sveditor.ui.editor.outline;

import net.sf.sveditor.core.db.index.SVDBFilePath;

import net.sf.sveditor.core.db.SVDBFile;

public class SVOutlineContent {
	private SVDBFile				fFile;
	private SVDBFilePath			fFilePath;
	
	public SVOutlineContent(SVDBFile file, SVDBFilePath path) {
		fFile = file;
		fFilePath = path;
	}

	public SVDBFile getFile() {
		return fFile;
	}
	
	public SVDBFilePath getFilePath() {
		return fFilePath;
	}

	@Override
	public int hashCode() {
		int hash = 0;
		
		if (fFile != null) {
			hash += fFile.hashCode();
		}
		
		if (fFilePath != null) {
			hash += fFilePath.hashCode();
		}
		
		return hash;
	}
	
}
