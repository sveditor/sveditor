package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBCoverCrossBinsSel extends SVDBItem {
	
	private SVExpr				fSelectExpr;
	
	public SVDBCoverCrossBinsSel(SVDBIdentifier id) {
		super(id.getId(), SVDBItemType.CoverCrossBinsSel);
	}
	
	public void setSelectExpr(SVExpr expr) {
		fSelectExpr = expr;
	}
	
	public SVExpr getSelectExpr() {
		return fSelectExpr;
	}

}
