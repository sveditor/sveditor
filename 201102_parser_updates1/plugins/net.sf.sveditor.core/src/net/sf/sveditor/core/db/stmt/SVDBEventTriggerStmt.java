package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBEventTriggerStmt extends SVDBStmt {
	private SVDBStmt			fDelayOrEventControl;
	private SVDBExpr				fHierarchicalEventIdentifier;
	
	public SVDBEventTriggerStmt() {
		super(SVDBItemType.EventTriggerStmt);
	}
	
	public SVDBStmt getDelayOrEventControl() {
		return fDelayOrEventControl;
	}
	
	public void setDelayOrEventControl(SVDBStmt stmt) {
		fDelayOrEventControl = stmt;
	}
	
	public SVDBExpr getHierarchicalEventIdentifier() {
		return fHierarchicalEventIdentifier;
	}
	
	public void setHierarchicalEventIdentifier(SVDBExpr expr) {
		fHierarchicalEventIdentifier = expr;
	}

}
