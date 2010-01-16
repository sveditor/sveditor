package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public class SVDBProgramBlock extends SVDBScopeItem {
	
	public SVDBProgramBlock(String name) {
		super(name, SVDBItemType.Program);
	}
	
	public SVDBProgramBlock(
			SVDBFile			file,
			SVDBScopeItem		parent,
			SVDBItemType		type,
			IDBReader			reader) throws DBFormatException {
		super(file, parent, type, reader);
	}

}
