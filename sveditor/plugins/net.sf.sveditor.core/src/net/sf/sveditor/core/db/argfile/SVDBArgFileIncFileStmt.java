package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileIncFileStmt extends SVDBArgFileStmt {
	public String					fPath;
	
	public SVDBArgFileIncFileStmt() {
		super(SVDBItemType.ArgFileIncFileStmt);
	}

	public SVDBArgFileIncFileStmt(String path) {
		this();
		fPath = path;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public void setPath(String path) {
		fPath = path;
	}
}
