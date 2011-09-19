package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVDBTypeExpr extends SVDBExpr {
	private SVDBTypeInfo			fTypeInfo;
	
	public SVDBTypeExpr() {
		super(SVDBItemType.TypeExpr);
	}
	
	public SVDBTypeExpr(SVDBTypeInfo type) {
		this();
		fTypeInfo = type;
	}
	
	public void setTypeInfo(SVDBTypeInfo type) {
		fTypeInfo = type;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}

}
