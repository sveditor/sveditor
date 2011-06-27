package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public interface ISVExprPersistenceFactory {
	
	SVDBExpr readSVExpr(
			SVDBItemType			type,
			IDBReader			reader) throws DBFormatException;

}
