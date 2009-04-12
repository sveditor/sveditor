package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTaskFuncParam extends SVDBVarDeclItem {
	
	public SVDBTaskFuncParam(String type, String name) {
		super(type, name, SVDBItemType.TaskFuncParam);
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBTaskFuncParam(fTypeName, getName());
		
		init(ret);
		
		return ret;
	}
	
	public SVDBTaskFuncParam(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
	}
	
	
}
