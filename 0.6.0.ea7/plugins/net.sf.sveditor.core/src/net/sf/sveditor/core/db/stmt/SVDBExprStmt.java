package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBExprStmt extends SVDBStmt {
	private SVDBExpr				fExpr;
	
	public SVDBExprStmt() {
		super(SVDBItemType.ExprStmt);
	}
	
	public SVDBExprStmt(SVDBExpr expr) {
		super(SVDBItemType.ExprStmt);
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

}
