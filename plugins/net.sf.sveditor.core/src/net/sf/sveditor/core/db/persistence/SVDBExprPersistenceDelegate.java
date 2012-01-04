package net.sf.sveditor.core.db.persistence;

import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBExprPersistenceDelegate implements ISVDBPersistenceRWDelegate {
	private ISVDBPersistenceRWDelegateParent			fParent;

	public void init(ISVDBPersistenceRWDelegateParent parent) {
		fParent = parent;
		// TODO Auto-generated method stub

	}

	public Set<Class> getSupportedObjects() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<Class> getSupportedEnumTypes() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<SVDBItemType> getSupportedItemTypes() {
		// TODO Auto-generated method stub
		return null;
	}

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeEnumType(Class cls, Enum value) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void readObject(ISVDBChildItem parent, Class cls, Object obj)
			throws DBFormatException {
		// TODO Auto-generated method stub

	}

	public ISVDBItemBase readSVDBItem(SVDBItemType type, ISVDBChildItem parent)
			throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

}
