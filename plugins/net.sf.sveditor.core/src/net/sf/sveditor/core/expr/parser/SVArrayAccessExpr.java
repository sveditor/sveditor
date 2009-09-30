package net.sf.sveditor.core.expr.parser;

public class SVArrayAccessExpr extends SVExpr {
	private SVExpr				fLhs;
	private SVExpr				fLow;
	private SVExpr				fHigh;
	
	public SVArrayAccessExpr(SVExpr lhs, SVExpr low, SVExpr high) {
		super(SVExprType.ArrayAccess);
		
		fLhs   = lhs;
		fLow   = low;
		fHigh  = high;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public SVExpr getLow() {
		return fLow;
	}
	
	public SVExpr getHigh() {
		return fHigh;
	}
	
}
