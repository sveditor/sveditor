package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverCrossBinsSel extends SVDBItem {
	
	private SVDBExpr				fSelectExpr;
	
	public SVDBCoverCrossBinsSel() {
		super("", SVDBItemType.CoverCrossBinsSel);
	}
	
	public SVDBCoverCrossBinsSel(SVDBIdentifier id) {
		super(id.getId(), SVDBItemType.CoverCrossBinsSel);
	}
	
	public void setSelectExpr(SVDBExpr expr) {
		fSelectExpr = expr;
	}
	
	public SVDBExpr getSelectExpr() {
		return fSelectExpr;
	}

}
