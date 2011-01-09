package net.sf.sveditor.core.db.expr;

public class SVAssignmentPatternRepeatExpr extends SVAssignmentPatternExpr {
	private SVExpr					fRepeatExpr;
	
	public SVAssignmentPatternRepeatExpr(SVExpr repeat_expr) {
		super();
		fRepeatExpr = repeat_expr;
	}

	public SVExpr getRepeatExpr() {
		return fRepeatExpr;
	}
}
