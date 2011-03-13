package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBRepeatStmt extends SVDBBodyStmt {
	
	private SVDBExpr				fRepeatExpr;

	public SVDBRepeatStmt() {
		super(SVDBItemType.RepeatStmt);
	}
	
	public void setExpr(SVDBExpr expr) {
		fRepeatExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fRepeatExpr;
	}
	
}
