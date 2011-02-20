package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public interface ISVDBStmtPersistenceFactory {
	
	SVDBStmt readSVDBStmt(
			ISVDBChildItem		parent,
			SVDBStmtType		stmt_type,
			IDBReader			reader) throws DBFormatException;

}
