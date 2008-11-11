package net.sf.sveditor.core.db;

public class SVDBFieldItem extends SVDBItem implements IFieldItemAttr {
	
	protected int					fFieldAttr;
	
	public SVDBFieldItem(String name, SVDBItemType type) {
		super(name, type);
	}
	
	public int getAttr() {
		return fFieldAttr;
	}
	
	public void setAttr(int attr) {
		fFieldAttr = attr;
	}
	
	public SVDBItem duplicate() {
		SVDBFieldItem ret = new SVDBFieldItem(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		fFieldAttr = ((SVDBFieldItem)other).fFieldAttr;
	}

}
