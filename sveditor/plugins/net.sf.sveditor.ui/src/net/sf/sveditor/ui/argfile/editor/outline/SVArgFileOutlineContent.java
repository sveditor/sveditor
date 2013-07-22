package net.sf.sveditor.ui.argfile.editor.outline;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.SVDBFilePath;

public class SVArgFileOutlineContent {
	private SVDBFile				fFile;
	private SVDBFilePath			fFilePath;
	
	public SVArgFileOutlineContent(SVDBFile file, SVDBFilePath path) {
		fFile = file;
		fFilePath = path;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public SVDBFilePath getFilePath() {
		return fFilePath;
	}
	
}
