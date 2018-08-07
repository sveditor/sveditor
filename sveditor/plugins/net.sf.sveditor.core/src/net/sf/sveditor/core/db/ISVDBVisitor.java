package net.sf.sveditor.core.db;

public interface ISVDBVisitor {

	void visit_alias(SVDBAlias a);
	
	void visit_assign(SVDBAssign a);
	
	void visit_assign_item(SVDBAssignItem a);
	
	void visit_bind(SVDBBind b);
	
	void visit_class_decl(SVDBClassDecl c);
	
	void visit_clocking_block(SVDBClockingBlock b);
	
	void visit_package_decl(SVDBPackageDecl p);

}
