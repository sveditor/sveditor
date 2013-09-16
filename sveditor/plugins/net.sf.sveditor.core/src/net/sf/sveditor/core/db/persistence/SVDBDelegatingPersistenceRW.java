/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

@SuppressWarnings({"unchecked","rawtypes"})
public class SVDBDelegatingPersistenceRW extends SVDBPersistenceRWBase
	implements IDBReader, IDBWriter, ISVDBPersistenceRWDelegateParent {
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
		fDefaultDelegate.init(this, fIn, fOut);
	}
	
	@Override
	public void init(DataInput in) {
		super.init(in);
		for (ISVDBPersistenceRWDelegate d : fDelegateList) {
			d.init(this, in, null);
		}
		fDefaultDelegate.init(this, in, null);
	}

	@Override
	public void init(DataOutput out) {
		super.init(out);
		for (ISVDBPersistenceRWDelegate d : fDelegateList) {
			d.init(this, null, out);
		}
		fDefaultDelegate.init(this, null, out);
	}

	public void addDelegate(ISVDBPersistenceRWDelegate d) {
		fDelegateList.add(d);
		
		d.init(this, fIn, fOut);
		Set<Class<?>> supported_classes = d.getSupportedObjects();
		
		if (supported_classes != null) {
			for (Class cls : supported_classes) {
				fObjectDelegateMap.put(cls, d);
			}
		}
		
		Set<Class<?>> supported_enums = d.getSupportedEnumTypes();
		
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

	public Map<String, List> readMapStringList(Class val_c) throws DBFormatException {
		Map<String, List> ret = new HashMap<String, List>();
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_MAP) {
			throw new DBFormatException("Expecting TYPE_MAP ; received " + type);
		}
		
		int size = readInt();
		for (int i=0; i<size; i++) {
			String key = readString();
			ret.put(key, readObjectList(null, val_c));
		}
		
		return ret;
	}

	public Map<String, Object> readMapStringObject(Class val_c) throws DBFormatException {
		Map<String, Object> ret = new HashMap<String, Object>();
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_MAP) {
			throw new DBFormatException("Expecting TYPE_MAP ; received " + type);
		}
		
		int size = readInt();
		for (int i=0; i<size; i++) {
			String key = readString();
			Object val = null;
			try {
				val = val_c.newInstance();
			} catch (InstantiationException e) {
				throw new DBFormatException("Fail to create instance of class " + val_c.getName());
			} catch (IllegalAccessException e) {
				throw new DBFormatException("Fail to create instance of class " + val_c.getName());
			}
			readObject(null, val_c, val);
			ret.put(key, val);
		}
		
		return ret;
	}

	public void writeMapStringList(Map<String, List> map, Class list_c) 
			throws DBWriteException, DBFormatException {
		if (map == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_MAP);
			
			writeInt(map.size());
			for (Entry<String, List> e : map.entrySet()) {
				writeString(e.getKey());
				writeObjectList(e.getValue(), list_c);
			}
		}
	}

	public void writeMapStringObject(Map<String, Object> map, Class obj_c)
			throws DBWriteException, DBFormatException {
		if (map == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_MAP);
			
			writeInt(map.size());
			for (Entry<String, Object> e : map.entrySet()) {
				writeString(e.getKey());
				writeObject(obj_c, e.getValue());
			}
		}
	}

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		ISVDBPersistenceRWDelegate d = fObjectDelegateMap.get(cls);
		
		if (d != null) {
			d.writeObject(cls, obj);
		} else {
//			System.out.println("[WRITE] Using default for \"" + cls.getName() + "\"");
			fDefaultDelegate.writeObject(cls, obj);
		}
	}

	public void writeObjectList(List items, Class obj_c) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_OBJECT_LIST);
			writeInt(items.size());
		
			for (Object v : items) {
				writeObject(obj_c, v);
			}
		}
	}
	
	public List readObjectList(ISVDBChildParent parent, Class val_c) throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		} else if (type != TYPE_OBJECT_LIST) {
			throw new DBFormatException("Expect TYPE_OBJECT_LIST, receive " + type + " class " + val_c.getName());
		}
		int size = readInt();
		List ret = new ArrayList();
		for (int i=0; i<size; i++) {
			Object val = null;
			try {
				val = val_c.newInstance();
			} catch (InstantiationException e) {
				throw new DBFormatException("Fail to create instance of class " + val_c.getName());
			} catch (IllegalAccessException e) {
				throw new DBFormatException("Fail to create instance of class " + val_c.getName());
			}
			readObject(parent, val_c, val);
			ret.add(val);
		}
		
		return ret;
	}

	public void writeItemType(SVDBItemType type) throws DBWriteException {
		writeEnumType(SVDBItemType.class, type);
	}

	public void writeEnumType(Class<?> enum_type, Enum<?> value)
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
//			System.out.println("[READ] Using default for \"" + cls.getName() + "\"");
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
