package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBDoWhileStmt extends SVDBBodyStmt {
	private SVDBExpr			fCond;
	
	public SVDBDoWhileStmt() {
		super(SVDBItemType.DoWhileStmt);
	}
	
	public void setCond(SVDBExpr cond) {
		fCond = cond;
	}
	
	public SVDBExpr getCond() {
		return fCond;
	}
	
}
