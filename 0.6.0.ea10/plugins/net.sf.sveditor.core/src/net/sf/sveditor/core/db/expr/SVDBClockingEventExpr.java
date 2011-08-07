package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBClockingEventExpr extends SVDBExpr {
	private SVDBExpr			fExpr;
	
	public SVDBClockingEventExpr() {
		super(SVDBItemType.ClockingEventExpr);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
