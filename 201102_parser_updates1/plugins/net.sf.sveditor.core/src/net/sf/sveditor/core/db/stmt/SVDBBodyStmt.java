package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBBodyStmt extends SVDBStmt {
	private SVDBStmt			fBody;
	
	protected SVDBBodyStmt(SVDBItemType stmt_type) {
		super(stmt_type);
	}
	
	public void setBody(SVDBStmt stmt) {
		fBody = stmt;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}
}
