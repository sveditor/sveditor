package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBNameMappedExpr extends SVDBExpr {
	private String				fName;
	private SVDBExpr			fExpr;
	
	public SVDBNameMappedExpr() {
		super(SVDBItemType.NameMappedExpr);
	}
	
	public SVDBNameMappedExpr(String name, SVDBExpr expr) {
		this();
		fName = name;
		fExpr = expr;
	}
	
	public String getName() {
		return fName;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
