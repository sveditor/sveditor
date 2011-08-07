package net.sf.sveditor.core.db;

public class SVDBModIfcInstItem extends SVDBItem {
	private SVDBParamValueAssignList		fPortMap;
	
	
	public SVDBModIfcInstItem() {
		super("", SVDBItemType.ModIfcInstItem);
	}
	
	public SVDBModIfcInstItem(String name) {
		super(name, SVDBItemType.ModIfcInstItem);
	}
	
	public SVDBParamValueAssignList getPortMap() {
		return fPortMap;
	}
	
	public void setPortMap(SVDBParamValueAssignList map) {
		fPortMap = map;
	}

}
