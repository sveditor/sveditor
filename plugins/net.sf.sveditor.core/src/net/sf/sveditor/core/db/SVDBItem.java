package net.sf.sveditor.core.db;

public class SVDBItem {
	private SVDBScopeItem			fParent;
	private String					fName;
	private SVDBItemType			fType;
	private SVDBLocation			fLocation;
	
	public SVDBItem(String name, SVDBItemType type) {
		fName = name;
		fType = type;
		fLocation = null;
	}
	
	public SVDBLocation getLocation() {
		return fLocation;
	}
	
	public void setLocation(SVDBLocation loc) {
		fLocation = loc;
	}
	
	public void setParent(SVDBScopeItem parent) {
		fParent = parent;
	}
	
	public SVDBScopeItem getParent() {
		return fParent;
	}

	public String getName() {
		return fName;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBItem(fName, fType);
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		fName   = other.fName;
		fParent = other.fParent;
		fType   = other.fType;
	}
	
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		} else if (obj instanceof SVDBItem) {
			SVDBItem other = (SVDBItem)obj;
			boolean ret = true;
			
			if (other.fName == null || fName == null) {
				ret &= other.fName == fName;
			} else {
				ret &= other.fName.equals(fName);
			}
			if (other.fType == null || fType == null) {
				ret &= other.fType == fType;
			} else {
				ret &= other.fType.equals(fType);
			}
			return ret;
		} else {
			return super.equals(obj);
		}
	}
}
