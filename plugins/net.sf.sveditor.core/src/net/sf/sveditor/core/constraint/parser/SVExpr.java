package net.sf.sveditor.core.constraint.parser;

public class SVExpr {
	
	protected SVExprType			fType;
	
	public SVExpr(SVExprType type) {
		fType = type;
	}
	
	public SVExprType getType() {
		return fType;
	}
	

}
