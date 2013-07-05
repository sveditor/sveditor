package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileSrcLibFileStmt extends SVDBArgFileStmt {
	public String				fSrcLibFile;
	
	public SVDBArgFileSrcLibFileStmt() {
		super(SVDBItemType.ArgFileSrcLibFileStmt);
	}
	
	public SVDBArgFileSrcLibFileStmt(String path) {
		this();
		fSrcLibFile = path;
	}

	public String getSrcLibFile() {
		return fSrcLibFile;
	}
	
	public void setSrcLibFile(String path) {
		fSrcLibFile = path;
	}
}
