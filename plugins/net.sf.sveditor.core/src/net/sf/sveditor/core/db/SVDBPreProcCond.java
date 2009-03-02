package net.sf.sveditor.core.db;


public class SVDBPreProcCond extends SVDBScopeItem {
	
	private String						fConditional;
	
	public SVDBPreProcCond(String name, String conditional) {
		super(name, SVDBItemType.PreProcCond);
		fConditional = conditional;
	}
	
	public String getConditional() {
		return fConditional;
	}
	
	public SVDBItem duplicate() {
		SVDBPreProcCond ret = new SVDBPreProcCond(getName(), fConditional);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}
	
	public boolean equals(Object obj) {
		if (super.equals(obj) && obj instanceof SVDBPreProcCond) {
			return fConditional.equals(((SVDBPreProcCond)obj).fConditional);
		}
		return false;
	}
}
