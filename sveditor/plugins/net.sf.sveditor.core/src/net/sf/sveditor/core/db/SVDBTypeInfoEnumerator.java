package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBTypeInfoEnumerator extends SVDBTypeInfo {
	public SVDBExpr				fExpr;
	
	public SVDBTypeInfoEnumerator() {
		this("");
	}
	
	public SVDBTypeInfoEnumerator(String name) {
		super(name, SVDBItemType.TypeInfoEnumerator);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_type_info_enumerator(this);
	}
	
}
