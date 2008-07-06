package net.sf.sveditor.core.db;

public class SVDBTaskFuncParam extends SVDBItem {
	
	private String			fTypeName;
	
	public SVDBTaskFuncParam(String type, String name) {
		super(name, SVDBItemType.TaskFuncParam);
		fTypeName = type;
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBTaskFuncParam(fTypeName, getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		fTypeName = ((SVDBTaskFuncParam)other).fTypeName;
	}
	
	public String getTypeName() {
		return fTypeName;
	}

}
