package net.sf.sveditor.core.db.expr;

public class SVNullLiteralExpr extends SVExpr {
	
	public SVNullLiteralExpr() {
		super(SVExprType.Null);
	}
	
	public SVNullLiteralExpr duplicate() {
		SVNullLiteralExpr ret = new SVNullLiteralExpr();
		
		ret.init(this);
		
		return ret;
	}

}
