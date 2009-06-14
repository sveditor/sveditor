package net.sf.sveditor.core.constraint.parser;

public class SVArrayAccessExpr extends SVExpr {
	private SVExpr				fLhs;
	private SVExpr				fIndex;
	
	public SVArrayAccessExpr(SVExpr lhs, SVExpr index) {
		fLhs   = lhs;
		fIndex = index;
	}

}
