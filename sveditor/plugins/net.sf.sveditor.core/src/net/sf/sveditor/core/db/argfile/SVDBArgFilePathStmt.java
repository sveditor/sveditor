package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFilePathStmt extends SVDBArgFileStmt {
	public String					fSrcPath;
	
	public SVDBArgFilePathStmt() {
		super(SVDBItemType.ArgFilePathStmt);
	}
	
	public SVDBArgFilePathStmt(String path) {
		this();
		fSrcPath = path;
	}
	
	public void setPath(String path) {
		fSrcPath = path;
	}
	
	public String getPath() {
		return fSrcPath;
	}
	
}
