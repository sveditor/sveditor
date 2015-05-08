package net.sf.sveditor.core.db;

public class SVDBUnprocessedRegion extends SVDBChildItem implements ISVDBEndLocation {
	public long				fEndLocation;
	
	public SVDBUnprocessedRegion() {
		super(SVDBItemType.UnprocessedRegion);
	}

	public long getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(long loc) {
		fEndLocation = loc;
	}
	
}
