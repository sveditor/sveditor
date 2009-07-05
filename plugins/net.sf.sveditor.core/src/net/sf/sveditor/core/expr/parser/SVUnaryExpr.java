package net.sf.sveditor.core.expr.parser;

public class SVUnaryExpr extends SVExpr {
	private SVExpr					fExpr;
	private String					fOp;
	
	public SVUnaryExpr(String op, SVExpr expr) {
		super(SVExprType.Unary);
		
		fOp = op;
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public String getOp() {
		return fOp;
	}

}
