package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileSrcLibPathStmt extends SVDBArgFileStmt {
	public String				fSrcLibPath;
	
	public SVDBArgFileSrcLibPathStmt() {
		super(SVDBItemType.ArgFileSrcLibPathStmt);
	}
	
	public SVDBArgFileSrcLibPathStmt(String path) {
		this();
		fSrcLibPath = path;
	}

	public String getSrcLibPath() {
		return fSrcLibPath;
	}
	
	public void setSrcLibPath(String path) {
		fSrcLibPath = path;
	}
}
