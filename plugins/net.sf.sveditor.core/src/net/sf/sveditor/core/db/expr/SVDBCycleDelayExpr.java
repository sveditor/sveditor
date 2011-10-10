package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCycleDelayExpr extends SVDBExpr {
	private SVDBExpr			fExpr;

	public SVDBCycleDelayExpr(SVDBItemType type) {
		super(type);
	}

	public SVDBCycleDelayExpr() {
		this(SVDBItemType.CycleDelayExpr);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
