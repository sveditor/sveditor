package net.sf.sveditor.core.constraint.parser;

public class SVParenExpr extends SVExpr {
	public SVExpr				fExpr;
	
	public SVParenExpr(SVExpr expr) {
		super(SVExprType.Paren);
		
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}

}
