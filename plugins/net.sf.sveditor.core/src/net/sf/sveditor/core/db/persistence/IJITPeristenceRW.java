package net.sf.sveditor.core.db.persistence;

import net.sf.sveditor.core.db.ISVDBChildItem;

public interface IJITPeristenceRW {
	
	void writeObject(Class cls, Object obj) throws DBWriteException;

	void readObject(ISVDBChildItem parent, Class cls, Object obj) throws DBFormatException;

}
