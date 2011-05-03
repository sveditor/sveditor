package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBWaitStmt extends SVDBBodyStmt {
	private SVDBExpr			fExpr;
	
	public SVDBWaitStmt() {
		this(SVDBItemType.WaitStmt);
	}
	
	protected SVDBWaitStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
}
