package net.sf.sveditor.core.db.expr;

public class SVNamedArgExpr extends SVExpr {
	private String			fArgName;
	private SVExpr			fExpr;
	
	public SVNamedArgExpr() {
		super(SVExprType.NamedArgExpr);
	}
	
	public void setArgName(String name) {
		fArgName = name;
	}
	
	public String getArgName() {
		return fArgName;
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}

}
