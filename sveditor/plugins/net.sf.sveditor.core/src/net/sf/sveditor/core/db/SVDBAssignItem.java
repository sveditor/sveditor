package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAssignItem extends SVDBChildItem {
	public SVDBExpr				fLHS;
	public SVDBExpr				fRHS;

	public SVDBAssignItem() {
		super(SVDBItemType.AssignItem);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setRHS(SVDBExpr rhs) {
		fRHS = rhs;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_assign_item(this);
	}
}
