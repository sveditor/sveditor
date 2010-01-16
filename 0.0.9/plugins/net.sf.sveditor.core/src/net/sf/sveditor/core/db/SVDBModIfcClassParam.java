package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBModIfcClassParam extends SVDBItem {
	
	public SVDBModIfcClassParam(String name) {
		super(name, SVDBItemType.ModIfcClassParam);
	}
	
	public SVDBModIfcClassParam(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBModIfcClassParam(getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}

}
