package net.sf.sveditor.core.db;

public class SVDBModuleDecl extends SVDBModIfcDecl {
	
	public SVDBModuleDecl() {
		super("", SVDBItemType.ModuleDecl);
	}
	
	public SVDBModuleDecl(String name) {
		super(name, SVDBItemType.ModuleDecl);
	}

}

