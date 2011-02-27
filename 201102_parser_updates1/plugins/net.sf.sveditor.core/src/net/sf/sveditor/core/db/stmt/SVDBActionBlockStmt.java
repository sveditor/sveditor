package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBActionBlockStmt extends SVDBStmt {
	
	public SVDBStmt					fStmt;
	public SVDBStmt					fElseStmt;
	
	public SVDBActionBlockStmt() {
		super(SVDBItemType.ActionBlockStmt);
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}
	
	public void setElseStmt(SVDBStmt stmt) {
		fElseStmt = stmt;
	}
	
	public SVDBStmt getElseStmt() {
		return fElseStmt;
	}

}
