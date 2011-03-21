package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;

public class SVDBCoverCrossBinsSel extends SVDBItem {
	
	private SVDBExpr				fSelectExpr;
	
	public SVDBCoverCrossBinsSel() {
		super("", SVDBItemType.CoverCrossBinsSel);
	}
	
	public SVDBCoverCrossBinsSel(SVDBIdentifierExpr id) {
		super(id, SVDBItemType.CoverCrossBinsSel);
	}
	
	public void setSelectExpr(SVDBExpr expr) {
		fSelectExpr = expr;
	}
	
	public SVDBExpr getSelectExpr() {
		return fSelectExpr;
	}

}
