package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBReturnStmt extends SVDBStmt {
	private SVExpr				fReturnExpr;
	
	public SVDBReturnStmt() {
		super(SVDBItemType.ReturnStmt);
	}
	
	public void setExpr(SVExpr expr) {
		fReturnExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fReturnExpr;
	}

}
