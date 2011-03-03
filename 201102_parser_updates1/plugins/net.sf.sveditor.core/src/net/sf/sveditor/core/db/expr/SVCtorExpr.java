package net.sf.sveditor.core.db.expr;

public class SVCtorExpr extends SVExpr {
	private SVExpr				fArgs[];
	private SVExpr				fDim;
	
	public SVCtorExpr() {
		super(SVExprType.CtorExpr);
	}
	
	public void setArgs(SVExpr args[]) {
		fArgs = args;
	}
	
	public SVExpr[] getArgs() {
		return fArgs;
	}
	
	public void setDim(SVExpr dim) {
		fDim = dim;
	}
	
	public SVExpr getDim() {
		return fDim;
	}

}
