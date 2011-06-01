package net.sf.sveditor.core.db;

public class SVDBModportClockingPortDecl extends SVDBModportPortsDecl {
	private String			fClockingId;
	
	public SVDBModportClockingPortDecl() {
		super(SVDBItemType.ModportClockingPortDecl);
	}
	
	public void setClockingId(String id) {
		fClockingId = id;
	}
	
	public String getClockingId() {
		return fClockingId;
	}

}
