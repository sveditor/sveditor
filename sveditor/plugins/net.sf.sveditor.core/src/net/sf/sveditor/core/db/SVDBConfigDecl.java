package net.sf.sveditor.core.db;

public class SVDBConfigDecl extends SVDBScopeItem {
	
	public SVDBConfigDecl() {
		super(null, SVDBItemType.ConfigDecl);
	}
	
	public SVDBConfigDecl(String name) {
		super(name, SVDBItemType.ConfigDecl);
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_config_decl(this);
	}

}
