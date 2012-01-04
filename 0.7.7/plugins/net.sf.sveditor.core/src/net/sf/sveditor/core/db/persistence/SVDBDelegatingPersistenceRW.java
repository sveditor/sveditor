package net.sf.sveditor.core.db.persistence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBDelegatingPersistenceRW extends SVDBPersistenceRWBase 
	implements IDBReader, IDBWriter {
	private Map<Class, ISVDBPersistenceRWDelegate>			fObjectDelegateMap;
	private Map<SVDBItemType, ISVDBPersistenceRWDelegate>	fSVDBItemDelegateMap;
	private Map<Class, ISVDBPersistenceRWDelegate>			fEnumDelegateMap;
	private List<ISVDBPersistenceRWDelegate>				fDelegateList;
	private ISVDBPersistenceRWDelegate						fDefaultDelegate;
	
	public SVDBDelegatingPersistenceRW() {
		fObjectDelegateMap = new HashMap<Class, ISVDBPersistenceRWDelegate>();
		fEnumDelegateMap = new HashMap<Class, ISVDBPersistenceRWDelegate>();
		fSVDBItemDelegateMap = new HashMap<SVDBItemType, ISVDBPersistenceRWDelegate>();
		fDelegateList = new ArrayList<ISVDBPersistenceRWDelegate>();
		fDefaultDelegate = new SVDBDefaultPersistenceRW();
		fDefaultDelegate.init(this);
		
		/*
		ISVDBPersistenceRWDelegate d = JITSVDBExprDelegateFactory.instance().newDelegate();
		d.init(this);
		 */
	}
	
	public void addDelegate(ISVDBPersistenceRWDelegate d) {
		fDelegateList.add(d);
		
		d.init(this);
		Set<Class> supported_classes = d.getSupportedObjects();
		
		if (supported_classes != null) {
			for (Class cls : supported_classes) {
				fObjectDelegateMap.put(cls, d);
			}
		}
		
		Set<Class> supported_enums = d.getSupportedEnumTypes();
		
		if (supported_enums != null) {
			for (Class cls : supported_enums) {
				fEnumDelegateMap.put(cls, d);
			}
		}
		
		Set<SVDBItemType> supported_types = d.getSupportedItemTypes();
		if (supported_types != null) {
			for (SVDBItemType type : supported_types) {
				fSVDBItemDelegateMap.put(type, d);
			}
		}
	}

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		ISVDBPersistenceRWDelegate d = fObjectDelegateMap.get(cls);
		
		if (d != null) {
			d.writeObject(cls, obj);
		} else {
			fDefaultDelegate.writeObject(cls, obj);
		}
	}

	public void writeItemType(SVDBItemType type) throws DBWriteException {
		writeEnumType(SVDBItemType.class, type);
	}

	public void writeEnumType(Class enum_type, Enum value)
			throws DBWriteException {
		
		if (value == null) {
			writeRawType(TYPE_NULL);
		} else {
			ISVDBPersistenceRWDelegate d = fEnumDelegateMap.get(enum_type);
		
			if (d != null) {
				d.writeEnumType(enum_type, value);
			} else {
				fDefaultDelegate.writeEnumType(enum_type, value);
			}
		}
	}

	public void writeItemList(List items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_ITEM_LIST);
			writeInt(items.size());
		
			for (Object it : items) {
				writeSVDBItem((ISVDBItemBase)it);
			}
		}
	}

	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
		if (item == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_ITEM);
			writeItemType(item.getType());
			
			ISVDBPersistenceRWDelegate d = fSVDBItemDelegateMap.get(item.getType());
			
			if (d != null) {
				d.writeSVDBItem(item);
			} else {
				fDefaultDelegate.writeSVDBItem(item);
			}
		}
	}

	public void setDebugEn(boolean en) {
		// TODO Auto-generated method stub
		
	}

	public void readObject(ISVDBChildItem parent, Class cls, Object obj)
			throws DBFormatException {
		ISVDBPersistenceRWDelegate d = fObjectDelegateMap.get(cls);
		
		if (d != null) {
			d.readObject(parent, cls, obj);
		} else {
			fDefaultDelegate.readObject(parent, cls, obj);
		}
	}

	public SVDBItemType readItemType() throws DBFormatException {
		return (SVDBItemType)readEnumType(SVDBItemType.class);
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		ISVDBPersistenceRWDelegate d = fEnumDelegateMap.get(enum_type);
		
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		if (type != TYPE_ENUM) {
			throw new DBFormatException("Expecting TYPE_ENUM ; received " + type);
		}

		if (d != null) {
			return d.readEnumType(enum_type);
		} else {
			return fDefaultDelegate.readEnumType(enum_type);
		}
	}

	public List readItemList(ISVDBChildItem parent) throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_ITEM_LIST) {
			throw new DBFormatException("Expect TYPE_ITEM_LIST, receive " + type);
		}
		
		int size = readInt();
		
		List ret = new ArrayList();
		for (int i=0; i<size; i++) {
			ret.add(readSVDBItem(parent));
		}
		
		return ret;
	}

	public ISVDBItemBase readSVDBItem(ISVDBChildItem parent)
			throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		} else if (type != TYPE_ITEM) {
			throw new DBFormatException("Expecting TYPE_ITEM ; received " + type);
		}
		
		SVDBItemType item_type = readItemType();
		ISVDBPersistenceRWDelegate d = fSVDBItemDelegateMap.get(item_type);
		
		if (d != null) {
			return d.readSVDBItem(item_type, parent);
		} else {
			return fDefaultDelegate.readSVDBItem(item_type, parent);
		}
	}
	

}
