package net.sf.sveditor.core.constraint.parser;

public class SVBinaryExpr extends SVExpr {
	private SVExpr				fLhs;
	private String				fOp;
	private SVExpr				fRhs;
	
	public SVBinaryExpr(SVExpr lhs, String op, SVExpr rhs) {
		super(SVExprType.Binary);
		
		fLhs = lhs;
		fOp = op;
		fRhs = rhs;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVExpr getRhs() {
		return fRhs;
	}

}
