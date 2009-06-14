package net.sf.sveditor.core.constraint.parser;

public class SVCastExpr extends SVExpr {
	private SVExpr					fCastType;
	private SVExpr					fExpr;
	
	public SVCastExpr(SVExpr cast_type, SVExpr expr) {
		super(SVExprType.Cast);
		
		fCastType = cast_type;
		fExpr = expr;
	}
	
	public SVExpr getCastType() {
		return fCastType;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
}
