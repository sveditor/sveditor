package net.sf.sveditor.core.expr.parser;

public class SVImplicationExpr extends SVConstraintExpr {
	
	private SVExpr					fExpr;
	private SVConstraintSetExpr		fConstraint;
	
	
	public SVImplicationExpr(SVExpr expr, SVConstraintSetExpr constraint) {
		super(SVExprType.Implication);
		fExpr 		= expr;
		fConstraint = constraint;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public SVConstraintSetExpr getConstraintSet() {
		return fConstraint;
	}

}
