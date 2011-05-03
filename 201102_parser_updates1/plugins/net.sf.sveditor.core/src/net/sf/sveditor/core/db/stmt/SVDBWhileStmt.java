package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBWhileStmt extends SVDBBodyStmt {
	private SVDBExpr				fCond;
	
	public SVDBWhileStmt() {
		super(SVDBItemType.WhileStmt);
	}
	
	public SVDBWhileStmt(SVDBExpr cond) {
		super(SVDBItemType.WhileStmt);
		fCond = cond;
	}
	
	public SVDBExpr getExpr() {
		return fCond;
	}
	
	public void setExpr(SVDBExpr expr) {
		fCond = expr;
	}
	
}
