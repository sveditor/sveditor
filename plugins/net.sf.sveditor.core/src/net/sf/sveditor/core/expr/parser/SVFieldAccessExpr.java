package net.sf.sveditor.core.expr.parser;

public class SVFieldAccessExpr extends SVExpr {
	private SVExpr 					fExpr;
	private String					fId;

	public SVFieldAccessExpr(SVExpr expr, String id) {
		super(SVExprType.FieldAccess);
		
		fExpr = expr;
		fId   = id;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public String getId() {
		return fId;
	}
}
