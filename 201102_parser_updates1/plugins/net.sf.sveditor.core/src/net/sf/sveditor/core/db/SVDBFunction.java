package net.sf.sveditor.core.db;


public class SVDBFunction extends SVDBTask {
	private SVDBTypeInfo				fRetType;

	public SVDBFunction() {
		super("", SVDBItemType.Function);
	}
	
	public SVDBFunction(String name, SVDBTypeInfo ret_type) {
		super(name, SVDBItemType.Function);
		fRetType = ret_type;
	}

	public SVDBTypeInfo getReturnType() {
		return fRetType;
	}
	
	public void setReturnType(SVDBTypeInfo ret) {
		fRetType = ret;
	}

	@Override
	public SVDBFunction duplicate() {
		return (SVDBFunction)super.duplicate();
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBFunction o = (SVDBFunction)other;
		fRetType = o.fRetType.duplicate(); 
	}
	
}
