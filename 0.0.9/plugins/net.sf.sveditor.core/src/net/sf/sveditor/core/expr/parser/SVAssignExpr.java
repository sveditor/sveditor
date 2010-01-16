package net.sf.sveditor.core.expr.parser;

public class SVAssignExpr extends SVExpr {
	private SVExpr					fLhs;
	private String					fOp;
	private SVExpr					fRhs;
	
	public SVAssignExpr(
			SVExpr			lhs,
			String			op,
			SVExpr			rhs) {
		super(SVExprType.Assign);
		
		fLhs = lhs;
		fOp  = op;
		fRhs = rhs;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVExpr getRhs() {
		return fRhs;
	}

}
