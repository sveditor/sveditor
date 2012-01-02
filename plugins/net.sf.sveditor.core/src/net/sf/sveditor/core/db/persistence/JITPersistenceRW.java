package net.sf.sveditor.core.db.persistence;

import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class JITPersistenceRW extends SVDBPersistenceRWBase implements IDBReader, IDBWriter {

	public void close() {
		// TODO Auto-generated method stub

	}

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeItemType(SVDBItemType type) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeEnumType(Class enum_type, Enum value)
			throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeItemList(Collection items) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void setDebugEn(boolean en) {
		// TODO Auto-generated method stub

	}

	public void readObject(ISVDBChildItem parent, Class cls, Object obj)
			throws DBFormatException {
		// TODO Auto-generated method stub

	}

	public SVDBItemType readItemType() throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	public List readItemList(ISVDBChildItem parent) throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	public ISVDBItemBase readSVDBItem(ISVDBChildItem parent)
			throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

}
