package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBDelayControlStmt extends SVDBStmt {
	
	private SVExpr				fExpr;
	private SVDBStmt			fStmt;
	
	public SVDBDelayControlStmt() {
		super(SVDBItemType.DelayControlStmt);
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
