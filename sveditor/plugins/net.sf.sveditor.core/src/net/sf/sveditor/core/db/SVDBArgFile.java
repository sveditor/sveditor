package net.sf.sveditor.core.db;

public class SVDBArgFile extends SVDBFile {
	
	public String				fBaseLocation;
	
	public SVDBArgFile() {
		this(null, null);
	}
	
	public SVDBArgFile(String path, String base) {
		super(path, SVDBItemType.ArgFile);
		fBaseLocation = (base != null)?base:"";
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public void setBaseLocation(String base) {
		fBaseLocation = base;
	}

}
