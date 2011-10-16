package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBSequenceClockingExpr extends SVDBExpr {
	private SVDBExpr 		fClockingExpr;
	private SVDBExpr		fSequenceExpr;
	
	public SVDBSequenceClockingExpr() {
		super(SVDBItemType.SequenceClockingExpr);
	}
	
	public void setClockingExpr(SVDBExpr expr) {
		fClockingExpr = expr;
	}
	
	public SVDBExpr getClockingExpr() {
		return fClockingExpr;
	}
	
	public void setSequenceExpr(SVDBExpr expr) {
		fSequenceExpr = expr;
	}
	
	public SVDBExpr getSequenceExpr() {
		return fSequenceExpr;
	}

}
