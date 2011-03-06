package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBConstraintForeachStmt extends SVDBStmt {
	private SVExpr				fExpr;
	private SVDBStmt			fStmt;
	
	public SVDBConstraintForeachStmt() {
		super(SVDBItemType.ConstraintForeachStmt);
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}

}
