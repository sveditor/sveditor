package net.sf.sveditor.core.db.persistence;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class JITPersistenceDelegateBase implements ISVDBPersistenceRWDelegate {
	protected Set<SVDBItemType>						fSupportedItems;
	protected ISVDBPersistenceRWDelegateParent		fParent; 
	
	public JITPersistenceDelegateBase() {
		fSupportedItems = new HashSet<SVDBItemType>();
	}
	
	public void init(Set<SVDBItemType> supported_items) {
		fSupportedItems.addAll(supported_items);
	}

	public void init(ISVDBPersistenceRWDelegateParent parent) {
		fParent = parent;
	}

	public Set<SVDBItemType> getSupportedItemTypes() {
		return fSupportedItems;
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

	public Set<Class> getSupportedObjects() {
		return null;
	}

	public Set<Class> getSupportedEnumTypes() {
		return null;
	}

}
