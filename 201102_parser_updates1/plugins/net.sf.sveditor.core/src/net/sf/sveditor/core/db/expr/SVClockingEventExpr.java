package net.sf.sveditor.core.db.expr;

public class SVClockingEventExpr extends SVExpr {
	private SVExpr			fExpr;
	
	public SVClockingEventExpr() {
		super(SVExprType.ClockingEventExpr);
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}

}
