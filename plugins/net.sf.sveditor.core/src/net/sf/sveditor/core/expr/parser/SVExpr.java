package net.sf.sveditor.core.expr.parser;

public class SVExpr {
	
	protected SVExprType			fType;
	
	public SVExpr(SVExprType type) {
		fType = type;
	}
	
	public SVExprType getType() {
		return fType;
	}
	

}
