package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBDisableStmt extends SVDBStmt {
	private SVExpr				fHierarchicalId;
	
	public SVDBDisableStmt() {
		super(SVDBItemType.DisableStmt);
	}
	
	public void setHierarchicalId(SVExpr expr) {
		fHierarchicalId = expr;
	}

	public SVExpr getHierarchicalId() {
		return fHierarchicalId;
	}
}
