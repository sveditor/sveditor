package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBModIfcInstItem extends SVDBVarDeclItem {
	
	public SVDBModIfcInstItem(String type, String name) {
		super(type, name, SVDBItemType.ModIfcInst);
	}
	
	public SVDBModIfcInstItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBModIfcInstItem(fTypeName, getName());
		
		init(ret);
		
		return ret;
	}
	
}
