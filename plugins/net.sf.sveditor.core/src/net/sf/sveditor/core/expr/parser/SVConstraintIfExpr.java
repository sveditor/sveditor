package net.sf.sveditor.core.expr.parser;

public class SVConstraintIfExpr extends SVConstraintExpr {
	private SVExpr					fIfExpr;
	private SVConstraintSetExpr		fConstraint;
	private SVConstraintSetExpr		fElse;
	
	public SVConstraintIfExpr(
			SVExpr 					expr,
			SVConstraintSetExpr		constraint,
			SVConstraintSetExpr		else_expr) {
		super(SVExprType.ConstraintIf);
		fIfExpr 	= expr;
		fConstraint = constraint;
		fElse		= else_expr;
	}
	
	public SVExpr getExpr() {
		return fIfExpr;
	}
	
	public SVConstraintSetExpr getConstraint() {
		return fConstraint;
	}
	
	public SVConstraintSetExpr getElseClause() {
		return fElse;
	}

}
