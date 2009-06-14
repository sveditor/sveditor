package net.sf.sveditor.core.constraint.parser;

public class SVBinaryExpr extends SVExpr {
	private SVExpr				fLhs;
	private String				fOp;
	private SVExpr				fRhs;
	
	public SVBinaryExpr(SVExpr lhs, String op, SVExpr rhs) {
		fLhs = lhs;
		fOp = op;
		fRhs = rhs;
	}

}
