package net.sf.sveditor.core.constraint.parser;

public class SVCastExpr extends SVExpr {
	private SVExpr					fCastType;
	private SVExpr					fExpr;
	
	public SVCastExpr(SVExpr cast_type, SVExpr expr) {
		fCastType = cast_type;
		fExpr = expr;
	}
	
}
