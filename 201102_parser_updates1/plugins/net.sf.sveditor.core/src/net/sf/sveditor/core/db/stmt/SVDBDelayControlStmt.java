package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBDelayControlStmt extends SVDBBodyStmt {
	
	private SVDBExpr				fExpr;
	
	public SVDBDelayControlStmt() {
		super(SVDBItemType.DelayControlStmt);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
}
