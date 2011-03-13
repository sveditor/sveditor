package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConstraintForeachStmt extends SVDBStmt {
	private SVDBExpr				fExpr;
	private SVDBStmt			fStmt;
	
	public SVDBConstraintForeachStmt() {
		super(SVDBItemType.ConstraintForeachStmt);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}

}
