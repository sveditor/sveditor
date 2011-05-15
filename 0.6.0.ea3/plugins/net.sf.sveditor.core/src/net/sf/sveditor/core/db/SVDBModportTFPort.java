package net.sf.sveditor.core.db;

public class SVDBModportTFPort extends SVDBChildItem {
	private String			fId;
	private SVDBTask		fTFPrototype;
	
	public SVDBModportTFPort() {
		super(SVDBItemType.ModportTFPort);
	}
	
	public void setId(String id) {
		fId = id;
	}
	
	public String getId() {
		return fId;
	}
	
	public void setPrototype(SVDBTask p) {
		fTFPrototype = p;
	}
	
	public SVDBTask getPrototype() {
		return fTFPrototype;
	}

}
