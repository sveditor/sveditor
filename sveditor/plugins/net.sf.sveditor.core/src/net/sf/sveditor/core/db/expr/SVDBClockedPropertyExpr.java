package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBClockedPropertyExpr extends SVDBExpr {
	public SVDBClockingEventExpr		fClockingExpr;
	public SVDBExpr						fPropertyExpr;
	
	public SVDBClockedPropertyExpr() {
		super(SVDBItemType.ClockedPropertyExpr);
	}
	
	public void setClockingExpr(SVDBClockingEventExpr expr) {
		fClockingExpr = expr;
	}
	
	public void setPropertyExpr(SVDBExpr expr) {
		fPropertyExpr = expr;
	}
	

}
