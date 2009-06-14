package net.sf.sveditor.core.constraint.parser;

public class SVIncDecExpr extends SVExpr {
	private SVExpr					fExpr;
	private String					fOp;
	
	public SVIncDecExpr(String op, SVExpr expr) {
		fExpr = expr;
		fOp   = op;
	}

}
