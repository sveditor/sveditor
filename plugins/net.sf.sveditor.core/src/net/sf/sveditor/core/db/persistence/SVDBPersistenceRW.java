package net.sf.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

@SuppressWarnings({"unchecked","rawtypes"})
public class SVDBPersistenceRW extends SVDBPersistenceRWBase implements IDBReader, IDBWriter,
		IDBPersistenceTypes {
	private LogHandle								fLog;
	private boolean									fIsWriter;
	private boolean									fDebugEn = false;
	private int										fLevel;
	private static Map<Class, Map<Integer, Enum>>	fIntToEnumMap;
	private static Map<Class, Map<Enum, Integer>>	fEnumToIntMap;
	private static Map<SVDBItemType, Class>			fClassMap;
	
	static {
		fIntToEnumMap = new HashMap<Class, Map<Integer,Enum>>();
		fEnumToIntMap = new HashMap<Class, Map<Enum,Integer>>();
	}
	
	public SVDBPersistenceRW() {
	}

	public void setDebugEn(boolean en) {
		fDebugEn = en;
	}
	
	public void init(DataInput in) {
		super.init(in);
		fIsWriter = false;
		fLog = LogFactory.getLogHandle("SVDBPersistenceReader");
		fLevel = 0;
		
		synchronized (getClass()) {
			if (fClassMap == null) {
				fClassMap 	= new HashMap<SVDBItemType, Class>();

				// Locate the class for each SVDBItemType element
				ClassLoader cl = getClass().getClassLoader();
				for (SVDBItemType v : SVDBItemType.values()) {
					String key = "SVDB" + v.name();
					Class cls = null;
					for (String pref : new String [] {"net.sf.sveditor.core.db.", 
							"net.sf.sveditor.core.db.stmt.",
					"net.sf.sveditor.core.db.expr."}) {
						try {
							cls = cl.loadClass(pref + key);
						} catch (Exception e) { }
					}

					if (cls == null) {
						System.out.println("Failed to locate class " + key);
					} else {
						fClassMap.put(v, cls);
					}
				}
			}
		}
	}

	public void init(DataOutput out) {
		super.init(out);
		fIsWriter = true;
		fLog = LogFactory.getLogHandle("SVDBPersistenceWriter");
		fLevel = 0;
	}
	
	public void close() {
		
	}
	
	public void writeObject(Class cls, Object target) throws DBWriteException {
		try {
			accessObject(null, cls, target);
		} catch (DBFormatException e) {}
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
			try {
				ret.put(key, readObjectList(null, val_c));
			} catch (DBWriteException e) {}
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

	public void readObject(ISVDBChildItem parent, Class cls, Object target) throws DBFormatException {
		try {
			accessObject(parent, cls, target);
		} catch (DBWriteException e) {}
	}

	public void accessObject(ISVDBChildItem parent, Class cls, Object target) throws DBWriteException, DBFormatException {
		if (fDebugEn) {
			debug("--> " + (++fLevel) + " accessObject: " + cls.getName());
		}
		
		if (cls.getSuperclass() != null && cls.getSuperclass() != Object.class) {
			accessObject(parent, cls.getSuperclass(), target);
		}
		
		Field fields[] = cls.getDeclaredFields();
		
		for (Field f : fields) {
			f.setAccessible(true);
			
			if (!Modifier.isStatic(f.getModifiers())) {
				
				if (f.getAnnotation(SVDBParentAttr.class) != null) {
					if (!fIsWriter) {
						try {
							f.set(target, parent);
						} catch (IllegalAccessException e) {
							e.printStackTrace();
						}
					}
					continue;
				}
				
				if (f.getAnnotation(SVDBDoNotSaveAttr.class) != null) {
					continue;
				}
				
				try {
					Class field_class = f.getType();
					Object field_value = null;
					
					if (fIsWriter) {
						field_value = f.get(target);
					}

					if (Enum.class.isAssignableFrom(field_class)) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an enum " + field_class.getName());
						}
						if (fIsWriter) {
							writeEnumType(field_class, (Enum)field_value);
						} else {
							f.set(target, readEnumType(field_class));
						}
					} else if (List.class.isAssignableFrom(field_class)) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							if (args.length != 1) {
								throw new DBFormatException("" + args.length + "-parameter list unsupported");
							}
							Class c = (Class)args[0];
							if (c == String.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<String>");
								}
								if (fIsWriter) {
									writeStringList((List<String>)field_value);
								} else {
									Object o = readStringList();
									f.set(target, o);
								}
							} else if (c == Integer.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<Integer>");
								}
								if (fIsWriter) {
									writeIntList((List<Integer>)field_value);
								} else {
									f.set(target, readIntList());
								}
							} else if (c == Long.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<Long>");
								}
								if (fIsWriter) {
									writeLongList((List<Long>)field_value);
								} else {
									f.set(target, readLongList());
								}
							} else if (ISVDBItemBase.class.isAssignableFrom(c)) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<ISVDBItemBase>");
								}
								if (fIsWriter) {
									writeItemList((Collection<ISVDBItemBase>)field_value);
								} else {
									if (target instanceof ISVDBChildItem) {
										f.set(target, readItemList((ISVDBChildItem)target));
									} else {
										f.set(target, readItemList(null));
									}
								}
							} else {
								if (fDebugEn) {
									debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is List<?>");
								}
								throw new DBFormatException("Type Arg: " + ((Class)args[0]).getName());
							}
						} else {
							if (fDebugEn) {
								debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unparameterized List");
							}
							throw new DBFormatException("Non-parameterized list");
						}
					} else if (Map.class.isAssignableFrom(field_class)) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							Class key_c = null;
							Class val_c = null;
							
							if (args[0] instanceof Class) {
								key_c = (Class)args[0];
							} else {
								throw new DBFormatException("Failed to deconstruct type for " +
										"field " + f.getName()); 
							}
							
							if (args[1] instanceof Class) {
								val_c = (Class)args[0];
							} else if (args[1] instanceof ParameterizedType) {
								val_c = (Class)((ParameterizedType)args[1]).getRawType();
							} else {
								throw new DBFormatException("Failed to deconstruct type for " +
										"field " + f.getName()); 
							}
							if (key_c == String.class && val_c == String.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is Map<String,String>");
								}
								if (fIsWriter) {
									writeMapStringString((Map<String, String>)field_value);
								} else {
									f.set(target, readMapStringString());
								}
							} else if (key_c == String.class && val_c.isAssignableFrom(List.class)) {
								Class c = (Class)((ParameterizedType)args[1]).getActualTypeArguments()[0];
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is Map<String,List>");
								}
								if (fIsWriter) {
									writeMapStringList((Map<String,List>)field_value, c);
								} else {
									f.set(target, readMapStringList(c));
								}
							} else {
								if (fDebugEn) {
									debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unrecognized Map<?,?>");
								}
								throw new DBFormatException("Map<" + key_c.getName() + ", " + val_c.getName() + ">: Class " + cls.getName());
							}
						} else {
							if (fDebugEn) {
								debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unparameterized map");
							}
							throw new DBFormatException("Non-parameterized map");
						}
					} else if (field_class == String.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is a String");
						}
						if (fIsWriter) {
							writeString((String)field_value);
						} else {
							f.set(target, readString());
						}
					} else if (field_class == int.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an Integer");
						}
						if (fIsWriter) {
							writeInt((Integer)field_value);
						} else {
							f.setInt(target, readInt());
						}
					} else if (field_class == long.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is a Long");
						}
						if (fIsWriter) {
							writeLong((Long)field_value);
						} else {
							f.setLong(target, readLong());
						}
					} else if (field_class == boolean.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is a Boolean");
						}
						if (fIsWriter) {
							writeBoolean((Boolean)field_value);
						} else {
							f.setBoolean(target, readBoolean());
						}
					} else if (SVDBLocation.class == field_class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an SVDBLocation");
						}
						if (fIsWriter) {
							writeSVDBLocation((SVDBLocation)field_value);
						} else {
							f.set(target, readSVDBLocation());
						}
					} else if (ISVDBItemBase.class.isAssignableFrom(field_class)) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an ISVDBItemBase");
						}
						if (fIsWriter) {
							writeSVDBItem((ISVDBItemBase)field_value);
						} else {
							f.set(target, readSVDBItem(parent));
						}
					} else {
						if (fDebugEn) {
							debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unknown class type " + field_class.getName());
						}
						throw new DBFormatException("Unhandled class " + field_class.getName());
					}
				} catch (IllegalAccessException e) {
					e.printStackTrace();
					throw new DBFormatException("Generic Load Failure: " + e.getMessage());
				}
			}
		}

		if (fDebugEn) {
			debug("<-- " + (fLevel--) + " accessObject: " + cls.getName());
		}
	}

	public void writeItemType(SVDBItemType type) throws DBWriteException {
		writeEnumType(SVDBItemType.class, type);
	}
	
	public void writeEnumType(Class enum_type, Enum value) throws DBWriteException {
		if (value == null) {
			writeRawType(TYPE_NULL);
		} else {
			synchronized (fEnumToIntMap) {
				if (!fEnumToIntMap.containsKey(enum_type)) {
					Enum vals[] = null;
					try {
						Method m = null;
						m = enum_type.getMethod("values");
						vals = (Enum[])m.invoke(null);
					} catch (Exception ex) {
						throw new DBWriteException("Enum class " + 
								enum_type.getName() + " does not have a values() method");
					}
					Map<Enum, Integer> em = new HashMap<Enum, Integer>();
					for (int i=0; i<vals.length; i++) {
						em.put(vals[i], i);
					}

					fEnumToIntMap.put(enum_type, em);
				}
				Map<Enum, Integer> em = fEnumToIntMap.get(enum_type);
				writeRawType(TYPE_ENUM);
				writeInt(em.get(value));
			}
		}
	}

	public void writeItemList(Collection items) throws DBWriteException {
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
			
			try {
				accessObject(null, item.getClass(), item);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	public void writeObjectList(List items, Class obj_c) throws DBWriteException, DBFormatException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_OBJECT_LIST);
			writeInt(items.size());
		
			for (Object v : items) {
				accessObject(null, obj_c, v);
			}
		}
	}
	
	private List readObjectList(ISVDBChildParent parent, Class val_c) throws DBWriteException, DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		} else if (type != TYPE_OBJECT_LIST) {
			throw new DBFormatException("Expect TYPE_OBJECT_LIST, receive " + type);
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
			accessObject(parent, val_c, val);
			ret.add(val);
		}
		
		return ret;
	}

	public SVDBItemType readItemType() throws DBFormatException {
		return (SVDBItemType)readEnumType(SVDBItemType.class);
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_ENUM) {
			throw new DBFormatException("Expecting TYPE_ENUM ; received " + type);
		}

		Enum ret;
		int val;
		synchronized (fIntToEnumMap) {
			if (!fIntToEnumMap.containsKey(enum_type)) {
				Enum vals[] = null;
				try {
					Method m = null;
					m = enum_type.getMethod("values");
					vals = (Enum[])m.invoke(null);
				} catch (Exception ex) {
					throw new DBFormatException("Enum class " + 
							enum_type.getName() + " does not have a values() method");
				}
				Map<Integer, Enum> em = new HashMap<Integer, Enum>();
				for (int i=0; i<vals.length; i++) {
					em.put(i, vals[i]);
				}

				fIntToEnumMap.put(enum_type, em);
			}
			Map<Integer, Enum> enum_vals = fIntToEnumMap.get(enum_type);
			val = readInt();
			ret = enum_vals.get(val); 
		}
		
		if (ret == null) {
			throw new DBFormatException("Value " + val + " does not exist in Enum " + enum_type.getName());
		}
		
		return ret;
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

	public ISVDBItemBase readSVDBItem(ISVDBChildItem parent) throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		} else if (type != TYPE_ITEM) {
			throw new DBFormatException("Expecting TYPE_ITEM ; received " + type);
		}
		
		SVDBItemType item_type   = readItemType();
		
		ISVDBItemBase ret = null;
		
		if (fClassMap.containsKey(item_type)) {
			Class cls = fClassMap.get(item_type);
			Object obj = null;
			try {
				obj = cls.newInstance();
			} catch (Exception e) {
				throw new DBFormatException("Failed to create object: " + item_type + " " + e.getMessage());
			}

			try {
				accessObject(parent, cls, obj);
			} catch (DBWriteException e) {}
			ret = (ISVDBItemBase)obj;
		} else {
			throw new DBFormatException("Unsupported SVDBItemType " + item_type);
		}

		return ret;
	}

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}

}
