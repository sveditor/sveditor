package net.sf.sveditor.core.db;

public class SVDBVisitorBase implements ISVDBVisitor {

	
	@Override
	public void visit_alias(SVDBAlias a) {
		
	}

	@Override
	public void visit_assign(SVDBAssign a) {
		for (SVDBAssignItem i : a.getAssignList()) {
			i.accept(this);
		}
	}

	@Override
	public void visit_assign_item(SVDBAssignItem a) {
		if (a.getLHS() != null) {
			a.getLHS().accept(this);
		}
		if (a.getRHS() != null) {
			a.getRHS().accept(this);
		}
	}
	
	@Override
	public void visit_bind(SVDBBind b) {
		// TODO Auto-generated method stub
	}
	
	@Override
	public void visit_class_decl(SVDBClassDecl c) {
		// TODO: visit base classes and interface classes

		// Visit the sub-items
		visit_scope(c);
	}
	

	@Override
	public void visit_clocking_block(SVDBClockingBlock b) {
		if (b.getExpr() != null) {
			b.getExpr().accept(this);
		}
		
		visit_scope(b);
		
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit_package_decl(SVDBPackageDecl p) {
		visit_scope(p);
	}

	protected void visit_scope(ISVDBChildParent p) {
		for (ISVDBChildItem c : p.getChildren()) {
			c.accept(this);
		}
	}
	
}
