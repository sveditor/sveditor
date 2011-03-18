package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public interface ISVExprPersistenceFactory {
	
	SVExpr readSVExpr(
			SVExprType			type,
			IDBReader			reader) throws DBFormatException;

}
