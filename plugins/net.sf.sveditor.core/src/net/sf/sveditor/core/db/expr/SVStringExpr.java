package net.sf.sveditor.core.db.expr;

public class SVStringExpr extends SVExpr {
	private String				fStr;
	
	public SVStringExpr(String str) {
		super(SVExprType.String);
		fStr = str;
	}
	
	public String getContent() {
		return fStr;
	}
	
	public SVStringExpr duplicate() {
		SVStringExpr ret = new SVStringExpr(fStr);
		
		ret.init(ret);
		
		return ret;
	}

}
