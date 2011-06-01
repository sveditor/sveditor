package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBNamedArgExpr extends SVDBExpr {
	private String				fArgName;
	private SVDBExpr			fExpr;
	
	public SVDBNamedArgExpr() {
		super(SVDBItemType.NamedArgExpr);
	}
	
	public void setArgName(String name) {
		fArgName = name;
	}
	
	public String getArgName() {
		return fArgName;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
