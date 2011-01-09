package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemBase;

public class SVExprString extends SVExpr {
	private String				fExprStr;
	
	public SVExprString(String expr) {
		super(SVExprType.ExprString);
		fExprStr = expr;
	}
	
	@Override
	public String toString() {
		return fExprStr;
	}

	@Override
	public SVDBItemBase duplicate() {
		SVExprString ret = new SVExprString(fExprStr);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		SVExprString o = (SVExprString)other;
		fExprStr = o.fExprStr;
	}
}
