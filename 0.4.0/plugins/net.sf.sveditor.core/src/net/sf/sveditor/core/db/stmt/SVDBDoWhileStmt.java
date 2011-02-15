package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBDoWhileStmt extends SVDBStmt {
	private SVExpr			fCond;
	private SVDBStmt		fBody;
	
	public SVDBDoWhileStmt() {
		super(SVDBStmtType.DoWhileStmt);
	}
	
	public void setCond(SVExpr cond) {
		fCond = cond;
	}
	
	public SVExpr getCond() {
		return fCond;
	}
	
	public void setBody(SVDBStmt body) {
		fBody = body;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}

}
