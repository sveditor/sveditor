package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBDisableStmt extends SVDBStmt {
	private SVDBExpr				fHierarchicalId;
	
	public SVDBDisableStmt() {
		this(SVDBItemType.DisableStmt);
	}
	
	protected SVDBDisableStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setHierarchicalId(SVDBExpr expr) {
		fHierarchicalId = expr;
	}

	public SVDBExpr getHierarchicalId() {
		return fHierarchicalId;
	}
}
