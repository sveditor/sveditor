package net.sf.sveditor.core.db;

public class SVDBTaskFuncParam extends SVDBVarDeclItem {
	
	public SVDBTaskFuncParam(String type, String name) {
		super(type, name, SVDBItemType.TaskFuncParam);
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBTaskFuncParam(fTypeName, getName());
		
		init(ret);
		
		return ret;
	}
	
}
