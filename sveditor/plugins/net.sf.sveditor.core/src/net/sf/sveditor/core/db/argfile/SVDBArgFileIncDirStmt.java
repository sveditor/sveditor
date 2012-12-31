package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileIncDirStmt extends SVDBArgFileStmt {
	
	public String				fIncludePath;
	
	public SVDBArgFileIncDirStmt() {
		super(SVDBItemType.ArgFileIncDirStmt);
	}
	
	public SVDBArgFileIncDirStmt(String path) {
		this();
		setIncludePath(path);
	}
	
	public void setIncludePath(String path) {
		fIncludePath = path;
	}
	
	public String getIncludePath() {
		return fIncludePath;
	}

}
