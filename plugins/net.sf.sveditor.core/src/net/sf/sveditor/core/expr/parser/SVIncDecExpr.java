package net.sf.sveditor.core.expr.parser;

public class SVIncDecExpr extends SVExpr {
	private SVExpr					fExpr;
	private String					fOp;
	
	public SVIncDecExpr(String op, SVExpr expr) {
		super(SVExprType.IncDec);
		
		fExpr = expr;
		fOp   = op;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public String getOp() {
		return fOp;
	}

}
