package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBPropertySpecExpr extends SVDBExpr {
	private SVDBClockingEventExpr			fClockingEventExpr;
	private SVDBExpr						fDisableExpr;
	private SVDBExpr						fExpr;
	
	public SVDBPropertySpecExpr() {
		super(SVDBItemType.PropertySpecExpr);
	}

	public SVDBClockingEventExpr getClockingEvent() {
		return fClockingEventExpr;
	}
	
	public void setClockingEvent(SVDBClockingEventExpr expr) {
		fClockingEventExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getDisableExpr() {
		return fDisableExpr;
	}
	
	public void setDisableExpr(SVDBExpr expr) {
		fDisableExpr = expr;
	}
}
