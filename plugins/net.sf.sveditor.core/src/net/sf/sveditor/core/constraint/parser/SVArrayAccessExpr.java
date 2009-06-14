package net.sf.sveditor.core.constraint.parser;

public class SVArrayAccessExpr extends SVExpr {
	private SVExpr				fLhs;
	private SVExpr				fIndex;
	
	public SVArrayAccessExpr(SVExpr lhs, SVExpr index) {
		super(SVExprType.ArrayAccess);
		
		fLhs   = lhs;
		fIndex = index;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public SVExpr getIndex() {
		return fIndex;
	}

}
