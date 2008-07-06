package net.sf.sveditor.core.db;

public class SVDBVarDeclItem extends SVDBFieldItem {
	private String				fTypeName;
	
	public SVDBVarDeclItem(String type, String name) {
		super(name, SVDBItemType.VarDecl);
		fTypeName = type;
	}
	
	public String getTypeName() {
		return fTypeName;
	}
	
	public SVDBItem duplicate() {
		SVDBVarDeclItem ret = new SVDBVarDeclItem(fTypeName, getName());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fTypeName = ((SVDBVarDeclItem)other).fTypeName;
	}

}
