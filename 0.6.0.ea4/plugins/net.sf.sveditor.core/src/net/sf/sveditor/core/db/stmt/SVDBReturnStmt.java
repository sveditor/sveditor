package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBReturnStmt extends SVDBStmt {
	private SVDBExpr				fReturnExpr;
	
	public SVDBReturnStmt() {
		super(SVDBItemType.ReturnStmt);
	}
	
	public void setExpr(SVDBExpr expr) {
		fReturnExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fReturnExpr;
	}

}
