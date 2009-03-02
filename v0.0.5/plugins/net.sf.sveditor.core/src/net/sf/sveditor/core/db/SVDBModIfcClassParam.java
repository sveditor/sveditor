package net.sf.sveditor.core.db;

public class SVDBModIfcClassParam extends SVDBItem {
	
	public SVDBModIfcClassParam(String name) {
		super(name, null);
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBModIfcClassParam(getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}

}
