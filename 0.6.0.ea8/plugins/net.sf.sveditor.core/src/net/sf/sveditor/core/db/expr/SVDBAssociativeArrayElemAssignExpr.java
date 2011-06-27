package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBAssociativeArrayElemAssignExpr extends SVDBExpr {
	private SVDBExpr				fKey;
	private SVDBExpr				fValue;
	
	public SVDBAssociativeArrayElemAssignExpr() {
		super(SVDBItemType.AssociativeArrayElemAssignExpr);
	}
	
	public void setKey(SVDBExpr key) {
		fKey = key;
	}
	
	public SVDBExpr getKey() {
		return fKey;
	}
	
	public void setValue(SVDBExpr val) {
		fValue = val;
	}
	
	public SVDBExpr getValue() {
		return fValue;
	}

}
