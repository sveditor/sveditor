package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBEventTriggerStmt extends SVDBStmt {
	private SVDBStmt			fDelayOrEventControl;
	private SVExpr				fHierarchicalEventIdentifier;
	
	public SVDBEventTriggerStmt() {
		super(SVDBItemType.EventTriggerStmt);
	}
	
	public SVDBStmt getDelayOrEventControl() {
		return fDelayOrEventControl;
	}
	
	public void setDelayOrEventControl(SVDBStmt stmt) {
		fDelayOrEventControl = stmt;
	}
	
	public SVExpr getHierarchicalEventIdentifier() {
		return fHierarchicalEventIdentifier;
	}
	
	public void setHierarchicalEventIdentifier(SVExpr expr) {
		fHierarchicalEventIdentifier = expr;
	}

}
