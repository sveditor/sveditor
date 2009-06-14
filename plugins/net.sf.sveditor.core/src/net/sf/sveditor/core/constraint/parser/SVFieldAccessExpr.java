package net.sf.sveditor.core.constraint.parser;

public class SVFieldAccessExpr extends SVExpr {
	private SVExpr 					fExpr;
	private String					fId;

	public SVFieldAccessExpr(SVExpr expr, String id) {
		fExpr = expr;
		fId   = id;
	}
}
