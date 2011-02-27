package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBEventControlStmt extends SVDBStmt {
	private SVExpr 				fExpr;
	
	public SVDBEventControlStmt() {
		super(SVDBItemType.EventControlStmt);
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}

}
