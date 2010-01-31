package net.sf.sveditor.core.expr.parser;

public class SVRangeExpr extends SVExpr {
	
	private SVExpr				fLeft;
	private SVExpr				fRight;
	
	public SVRangeExpr(SVExpr left, SVExpr right) {
		super(SVExprType.Range);
		fLeft  = left;
		fRight = right;
	}
	
	public SVExpr getLeft() {
		return fLeft;
	}
	
	public SVExpr getRight() {
		return fRight;
	}

}
