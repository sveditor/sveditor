package net.sf.sveditor.core.db.expr;


public class SVThisExpr extends SVExpr {
	
	public SVThisExpr() {
		super(SVExprType.This);
	}
	
	public SVThisExpr duplicate() {
		SVThisExpr ret = new SVThisExpr();
		ret.init(this);
		return ret;
	}

}
