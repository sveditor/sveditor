package net.sf.sveditor.core.constraint.parser;

public class SVUnaryExpr extends SVExpr {
	private SVExpr					fExpr;
	private String					fOp;
	
	public SVUnaryExpr(String op, SVExpr expr) {
		fOp = op;
		fExpr = expr;
	}

}
