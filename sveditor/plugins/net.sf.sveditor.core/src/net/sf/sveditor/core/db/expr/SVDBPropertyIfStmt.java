package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBPropertyIfStmt extends SVDBExpr {
	public SVDBExpr				fExpr;
	public SVDBExpr				fIfExpr;
	public SVDBExpr				fElseExpr;
	
	public SVDBPropertyIfStmt() {
		super(SVDBItemType.PropertyIfStmt);
	}

	public void setIfExpr(SVDBExpr expr) {
		fIfExpr = expr;
	}
	
	public SVDBExpr getIfExpr() {
		return fIfExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setElseExpr(SVDBExpr expr) {
		fElseExpr = expr;
	}
	
	public SVDBExpr getElseExpr() {
		return fElseExpr;
	}
}
