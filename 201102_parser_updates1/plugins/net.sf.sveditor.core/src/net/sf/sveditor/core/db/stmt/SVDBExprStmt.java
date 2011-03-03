package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBExprStmt extends SVDBStmt {
	private SVExpr				fExpr;
	
	public SVDBExprStmt(SVExpr expr) {
		super(SVDBItemType.ExprStmt);
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}

}
