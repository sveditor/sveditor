package net.sf.sveditor.core.db.expr;

import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCtorExpr extends SVDBExpr {
	private List<SVDBExpr>			fArgs;
	private SVDBExpr				fDim;
	
	public SVDBCtorExpr() {
		super(SVDBItemType.CtorExpr);
	}
	
	public void setArgs(List<SVDBExpr> args) {
		fArgs = args;
	}
	
	public List<SVDBExpr> getArgs() {
		return fArgs;
	}
	
	public void setDim(SVDBExpr dim) {
		fDim = dim;
	}
	
	public SVDBExpr getDim() {
		return fDim;
	}

}
