package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;

public class SVDBSequenceDistExpr extends SVDBExpr {
	private SVDBExpr					fExpr;
	private SVDBConstraintDistListStmt	fDistExpr;

	public SVDBSequenceDistExpr() {
		super(SVDBItemType.SequenceDistExpr);
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBConstraintDistListStmt getDistExpr() {
		return fDistExpr;
	}
	
	public void setDistExpr(SVDBConstraintDistListStmt dist) {
		fDistExpr = dist;
	}
}
