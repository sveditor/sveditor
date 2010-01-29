package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public class SVDBAssign extends SVDBItem {
	
	public SVDBAssign(String target) {
		super(target, SVDBItemType.Assign);
	}
	
	public SVDBAssign(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}
	
	public SVDBItem duplicate() {
		SVDBAssign ret = new SVDBAssign(getName());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}

}
