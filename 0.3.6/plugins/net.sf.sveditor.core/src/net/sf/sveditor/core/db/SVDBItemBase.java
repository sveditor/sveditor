package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.IDBWriter;


public class SVDBItemBase implements ISVDBItemBase {
	protected SVDBItemType			fType;
	protected SVDBLocation			fLocation;
	
	public SVDBItemBase(SVDBItemType type) {
		fType = type;
		fLocation = null;
	}

	public SVDBItemType getType() {
		return fType;
	}

	public SVDBLocation getLocation() {
		return fLocation;
	}

	public void setLocation(SVDBLocation location) {
		fLocation = location;
	}

	public void dump(IDBWriter writer) {
		writer.writeItemType(fType);
	}

	public SVDBItemBase duplicate() {
		SVDBItemBase ret = new SVDBItemBase(getType());
		ret.init(this);
		
		return ret;
	}

	public void init(SVDBItemBase other) {
		fType = other.fType;
		if (other.fLocation != null) {
			fLocation = other.fLocation.duplicate();
		} else {
			fLocation = null;
		}
	}
	
	public boolean equals(Object obj) {
		if (obj instanceof SVDBItemBase) {
			boolean ret = true;
			SVDBItemBase other = (SVDBItemBase)obj;
			
			if (other.fType == null || fType == null) {
				ret &= other.fType == fType;
			} else {
				ret &= other.fType.equals(fType);
			}

			if (fLocation == null || other.fLocation == null) {
				ret &= (fLocation == other.fLocation);
			} else {
				ret &= other.fLocation.equals(fLocation);
			}
			
			return ret;
		} else {
			return false;
		}
	}
	
	
	
}
