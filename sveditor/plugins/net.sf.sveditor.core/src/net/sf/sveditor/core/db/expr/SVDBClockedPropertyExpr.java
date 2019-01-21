package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.ISVDBVisitor;
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
	
	public SVDBClockingEventExpr getClockingExpr() {
		return fClockingExpr;
	}
	
	public void setPropertyExpr(SVDBExpr expr) {
		fPropertyExpr = expr;
	}
	
	public SVDBExpr getPropertyExpr() {
		return fPropertyExpr;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_clocked_property_expr(this);
	}

	

}
