package net.sf.sveditor.core.db.persistence;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBBaseItemsPersistenceDelegate implements
		ISVDBPersistenceRWDelegate {
	private Set<Class>								fSupportedObjects;
	private ISVDBPersistenceRWDelegateParent		fParent;
	
	public SVDBBaseItemsPersistenceDelegate() {
		fSupportedObjects = new HashSet<Class>();
		fSupportedObjects.add(SVDBItemBase.class);
	}

	public void init(ISVDBPersistenceRWDelegateParent parent) {
		fParent = parent;
	}

	public Set<Class> getSupportedObjects() {
		return fSupportedObjects;
	}

	public Set<Class> getSupportedEnumTypes() {
		return null;
	}
	
	public Set<SVDBItemType> getSupportedItemTypes() {
		return null;
	}

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		if (obj == null) {
			fParent.writeRawType(IDBPersistenceTypes.TYPE_NULL);
		} else if (cls == SVDBItemBase.class) {
			SVDBItemBase item = (SVDBItemBase)obj;
			fParent.writeSVDBLocation(item.getLocation());
		} else {
			throw new DBWriteException(getClass().getName() + " Unsupported writeObject class: " + cls.getName());
		}
	}


	public void readObject(ISVDBChildItem parent, Class cls, Object obj)
			throws DBFormatException {
		if (cls == SVDBItemBase.class) {
			SVDBItemBase item = (SVDBItemBase)obj;
			item.setLocation(fParent.readSVDBLocation());
		} else {
			throw new DBFormatException(getClass().getName() + " Unsupported readObject class: " + cls.getName());
		}
	}

	// Unsupported methods
	public void writeEnumType(Class cls, Enum value) throws DBWriteException {
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		return null;
	}

	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
	}

	public ISVDBItemBase readSVDBItem(SVDBItemType type, ISVDBChildItem parent)
			throws DBFormatException {
		return null;
	}
	
}
