package net.sf.sveditor.core.constraint.parser;

public class SVParenExpr extends SVExpr {
	public SVExpr				fExpr;
	
	public SVParenExpr(SVExpr expr) {
		fExpr = expr;
	}

}
