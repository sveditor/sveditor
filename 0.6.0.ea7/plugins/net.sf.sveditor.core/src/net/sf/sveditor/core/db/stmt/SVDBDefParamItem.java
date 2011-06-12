package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBDefParamItem extends SVDBStmt {
	private SVDBExpr			fTarget;
	private SVDBExpr			fExpr;
	
	public SVDBDefParamItem() {
		super(SVDBItemType.DefParamItem);
	}
	
	public void setTarget(SVDBExpr expr) {
		fTarget = expr;
	}
	
	public SVDBExpr getTarget() {
		return fTarget;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
