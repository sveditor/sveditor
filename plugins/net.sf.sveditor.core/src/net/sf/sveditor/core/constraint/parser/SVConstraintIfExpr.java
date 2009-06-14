package net.sf.sveditor.core.constraint.parser;

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

}
