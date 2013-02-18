package net.sf.sveditor.core.db;

public class SVDBUnprocessedRegion extends SVDBChildItem implements ISVDBEndLocation {
	public SVDBLocation				fEndLocation;
	
	public SVDBUnprocessedRegion() {
		super(SVDBItemType.UnprocessedRegion);
	}

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}
	
}
