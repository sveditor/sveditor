package net.sf.sveditor.core.constraint.parser;

public class SVQualifiedThisRefExpr extends SVExpr {
	private SVExpr 				fExpr;
	
	public SVQualifiedThisRefExpr(SVExpr expr) {
		super(SVExprType.QualifiedThisRef);
		
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}

}
