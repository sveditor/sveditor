package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.IDBWriter;

public interface ISVDBItemBase {
	
	SVDBItemType getType();
	
	SVDBLocation getLocation();
	
	void setLocation(SVDBLocation location);
	
	void dump(IDBWriter writer);
	
	SVDBItemBase duplicate();
	
	void init(SVDBItemBase other);
	

}
