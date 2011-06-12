/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.persistence;

import java.io.DataOutput;
import java.io.IOException;
import java.io.OutputStream;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;

@SuppressWarnings("rawtypes")
public class SVDBPersistenceWriter implements IDBWriter, IDBPersistenceTypes {
	private DataOutput							fBuf;
	private Map<Class, Map<Object, Integer>>	fEnumMap;
	private static final boolean				fDebugEn = false;
	private int									fLevel;
	
	public SVDBPersistenceWriter() {
		this(null);
	}
	
	private SVDBPersistenceWriter(OutputStream out) {
		fEnumMap = new HashMap<Class, Map<Object,Integer>>();
	}
	
	public void init(DataOutput out) {
		fBuf = out;
	}
	
	public void close() {
	}

	public void writeInt(int val) throws DBWriteException {
		try {
			if (val < 0) {
				if (val >= -0x000000FF) {
					fBuf.write((byte)TYPE_INT_8);
					fBuf.write((byte)val);
				} else if (val >= -0x0000FFFF) {
					fBuf.write((byte)TYPE_INT_16);
					fBuf.writeShort((short)val);
				} else { 
					fBuf.write((byte)TYPE_INT_32);
					fBuf.writeInt(val);
				}
			} else {
				if (val <= 0x0000007F) {
					fBuf.write((byte)TYPE_INT_8);
					fBuf.write((byte)val);
				} else if (val <= 0x00007FFF) {
					fBuf.write((byte)TYPE_INT_16);
					fBuf.writeShort((short)val);
				} else {
					fBuf.write((byte)TYPE_INT_32);
					fBuf.writeInt(val);
				}
			}
		} catch (IOException e) {
			throw new DBWriteException("writeInt failed: " + e.getMessage());
		}
	}
	
	public void writeBool(boolean v) throws DBWriteException {
		writeRawType((v)?TYPE_BOOL_TRUE:TYPE_BOOL_FALSE);
	}
	
	private void writeRawType(int type) throws DBWriteException {
		try {
			fBuf.write((byte)type);
		} catch (IOException e) {
			throw new DBWriteException("writeRawType failed: " + e.getMessage());
		}
	}

	public void writeIntList(List<Integer> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_INT_LIST);
			writeInt(items.size());
		
			for (Integer i: items) {
				writeInt(i.intValue());
			}
		}
	}

	public void writeItemList(Collection items) throws DBWriteException {
//		System.out.println("writeItemList");
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
	
	@SuppressWarnings("unchecked")
	public void writeObject(Class cls, Object item) throws DBWriteException {
		if (fDebugEn) {
			debug("--> " + (++fLevel) + " writeObject: " + cls.getName());
		}
		
		if (cls.getSuperclass() != null &&
				cls.getSuperclass() != Object.class) {
			writeObject(cls.getSuperclass(), item);
		}

		Field fields[] = cls.getDeclaredFields();

		for (Field f : fields) {
			f.setAccessible(true);
			if (!Modifier.isStatic(f.getModifiers())) {
				// Don't record the parent handle
				if (f.getAnnotation(SVDBParentAttr.class) != null) {
					continue;
				}
				if (f.getAnnotation(SVDBDoNotSaveAttr.class) != null) {
					continue;
				}
				
				
				try {
					Class field_class = f.getType();
					if (fDebugEn) {
						debug("  write field " + f.getName() + " in " + cls.getName() + ": " + field_class.getName());
					}
					Object field_value = f.get(item);
					
					if (field_value == null) {
						writeRawType(TYPE_NULL);
					} else if (Enum.class.isAssignableFrom(field_class)) {
						writeEnumType(field_class, (Enum)field_value);
					} else if (field_value instanceof List) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							Class c = (Class)args[0];
							if (fDebugEn) {
								debug("  write list field " + f.getName() + " w/item type " + c.getName());
							}
							if (c == String.class) {
								writeStringList((List)field_value);
							} else if (c == Integer.class) {
								writeIntList((List)field_value);
							} else if (ISVDBItemBase.class.isAssignableFrom(c)) {
								writeItemList((List)field_value);
							} else {
								throw new DBWriteException("Type Arg: " + ((Class)args[0]).getName());
							}
						} else {
							throw new DBWriteException("Non-parameterized list is unsupported");
						}
					} else if (field_value instanceof String) {
						writeString((String)field_value);
					} else if (field_value instanceof Integer) {
						writeInt(((Integer)field_value).intValue());
					} else if (field_value instanceof Long) {
						writeLong(((Long)field_value).longValue());
					} else if (field_value instanceof Boolean) {
						writeBool(((Boolean)field_value).booleanValue());
					} else if (field_value instanceof SVDBLocation) {
						SVDBLocation loc = (SVDBLocation)field_value;
						if (fDebugEn) {
							debug("    writeLocation: " + loc.getLine() + ":" + loc.getPos());
						}
						writeRawType(TYPE_SVDB_LOCATION);
						writeInt(loc.getLine());
						writeInt(loc.getPos());
					} else if (field_value instanceof ISVDBItemBase) {
						writeSVDBItem((ISVDBItemBase)field_value);
					} else if (field_value instanceof Map) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							Class key_c = (Class)args[0];
							Class val_c = (Class)args[1];
							if (key_c == String.class && val_c == String.class) {
								writeMapStringString((Map<String, String>)field_value);
							} else {
								throw new DBWriteException("Map<" + key_c.getName() + ", " + val_c.getName() + ">: Class " + cls.getName());
							}
						} else {
							throw new DBWriteException("Non-parameterized list is unsupported");
						}
					} else {
						throw new DBWriteException("Unsupported field: " + field_class.getName() + " in " + cls.getName());
					}
				} catch (IllegalAccessException e) {
					e.printStackTrace();
					throw new DBWriteException("Dump failure: " + e.getMessage());
				}
			}
		}
		if (fDebugEn) {
			debug("<-- " + (fLevel--) + " writeObject: " + cls.getName());
		}
	}
	
	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
		if (item == null) {
			writeRawType(TYPE_NULL);
		} else {
			if (fDebugEn) {
				debug("  writeSVDBItem: " + item.getType());
			}
			writeRawType(TYPE_ITEM);
			writeItemType(item.getType());
			
			try {
				writeObject(item.getClass(), item);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	public void writeItemType(SVDBItemType type) throws DBWriteException {
		writeEnumType(SVDBItemType.class, type);
	}
	
	@SuppressWarnings("unchecked")
	public void writeEnumType(Class enum_type, Enum value) throws DBWriteException {
		if (!fEnumMap.containsKey(enum_type)) {
			Object vals[] = null;
			try {
				Method m = null;
				m = enum_type.getMethod("values");
				vals = (Object[])m.invoke(null);
			} catch (Exception ex) {
				throw new DBWriteException("Enum class " + 
						enum_type.getName() + " does not have a values() method");
			}
			Map<Object, Integer> em = new HashMap<Object, Integer>();
			for (int i=0; i<vals.length; i++) {
				em.put(vals[i], i);
			}
			
			fEnumMap.put(enum_type, em);
		}
		Map<Object, Integer> em = fEnumMap.get(enum_type);
		writeRawType(TYPE_ENUM);
		writeInt(em.get(value));
	}
	
	private void writeMapStringString(Map<String, String> map) throws DBWriteException {
		writeRawType(TYPE_MAP);
		
		writeInt(map.size());
		for (Entry<String, String> e : map.entrySet()) {
			writeString(e.getKey());
			writeString(e.getValue());
		}
	}
	
	public void writeLong(long val) throws DBWriteException {
		try {
			if (val < 0) {
				if (val >= -0x00000000000000FFL) {
					fBuf.write(TYPE_INT_8);
					fBuf.writeByte((byte)val);
				} else if (val >= -0x000000000000FFFFL) {
					fBuf.write(TYPE_INT_16);
					fBuf.writeShort((short)val);
				} else if (val >= -0x00000000FFFFFFFFL) {
					fBuf.write(TYPE_INT_32);
					fBuf.writeInt((int)val);
				} else {
					fBuf.write(TYPE_INT_64);
					fBuf.writeLong(val);
				}
			} else {
				if (val <= 0x000000000000007FL) {
					fBuf.write(TYPE_INT_8);
					fBuf.writeByte((byte)val);
				} else if (val <= 0x0000000000007FFFL) {
					fBuf.write(TYPE_INT_16);
					fBuf.writeShort((short)val);
				} else if (val <= 0x000000007FFFFFFFL) {
					fBuf.write(TYPE_INT_32);
					fBuf.writeInt((int)val);
				} else {
					fBuf.write(TYPE_INT_64);
					fBuf.writeLong(val);
				}
			}
		} catch (IOException e) {
			throw new DBWriteException("writeLong failed: " + e.getMessage());
		}
	}

	public void writeString(String val) throws DBWriteException {
		if (val == null) {
			writeRawType(TYPE_NULL);
		} else {
			if (fDebugEn) {
				debug("    writeString: " + val);
			}
			try {
				writeRawType(TYPE_STRING);
				writeInt(val.length());
				fBuf.writeBytes(val);
			} catch (IOException e) {
				throw new DBWriteException("writeString failed: " + e.getMessage());
			}
		}
	}

	public void writeByteArray(byte data[]) throws DBWriteException {
		if (data == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_BYTE_ARRAY);
			writeInt(data.length);
			try {
				fBuf.write(data);
			} catch (IOException e) {
				throw new DBWriteException("writeByteArray failed: " + e.getMessage());
			}
		}
	}

	public void writeStringList(List<String> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_STRING_LIST);
			writeInt(items.size());
		
			for (String s: items) {
				writeString(s);
			}
		}
	}

	public void writeLongList(List<Long> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_LONG_LIST);
			writeInt(items.size());
		
			for (Long v : items) {
				writeLong(v.longValue());
			}
		}
	}

	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
