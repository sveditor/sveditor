package net.sf.sveditor.core.db.persistence;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

public interface ISVDBPersistenceFactory {
	
	SVDBItem readSVDBItem(
			IDBReader		reader,
			SVDBItemType 	type,
			SVDBFile		file,
			SVDBScopeItem	parent) throws DBFormatException;

}
