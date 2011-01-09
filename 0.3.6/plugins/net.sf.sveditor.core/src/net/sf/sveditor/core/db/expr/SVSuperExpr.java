package net.sf.sveditor.core.db.expr;


public class SVSuperExpr extends SVExpr {
	
	public SVSuperExpr() {
		super(SVExprType.Super);
	}
	
	public SVSuperExpr duplicate() {
		SVSuperExpr ret = new SVSuperExpr();
		ret.init(this);
		return ret;
	}

}
