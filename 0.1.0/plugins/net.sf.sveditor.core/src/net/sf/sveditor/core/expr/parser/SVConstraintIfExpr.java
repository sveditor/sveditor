package net.sf.sveditor.core.expr.parser;

public class SVConstraintIfExpr extends SVConstraintExpr {
	private SVExpr					fIfExpr;
	private SVConstraintSetExpr		fConstraint;
	private SVExpr					fElse;
	private boolean					fElseIf;
	
	public SVConstraintIfExpr(
			SVExpr 					expr,
			SVConstraintSetExpr		constraint,
			SVExpr					else_expr,
			boolean					else_if) {
		super(SVExprType.ConstraintIf);
		fIfExpr 	= expr;
		fConstraint = constraint;
		fElse		= else_expr;
		fElseIf 	= else_if;
	}
	
	public SVExpr getExpr() {
		return fIfExpr;
	}
	
	public SVConstraintSetExpr getConstraint() {
		return fConstraint;
	}
	
	public SVExpr getElseClause() {
		return fElse;
	}
	
	public boolean isElseIf() {
		return fElseIf;
	}

}
