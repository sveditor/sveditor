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
import net.sf.sveditor.core.db.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;

@SuppressWarnings("rawtypes")
public class SVDBPersistenceWriter implements IDBWriter, IDBPersistenceTypes {
	private OutputStream						fOutputStream;
	private byte								fBuf[];
	private int									fBufIdx;
	private Map<Class, Map<Object, Integer>>	fEnumMap;
	private static final boolean				fDebugEn = false;
	private int									fLevel;
	
	public SVDBPersistenceWriter(OutputStream out) {
		fOutputStream = out;
		fBuf = new byte[1024*1024];
		fEnumMap = new HashMap<Class, Map<Object,Integer>>();
	}
	
	public void init(OutputStream out) {
		fOutputStream = out;
		fBufIdx = 0;
	}
	
	public void close() {
		try {
			if (fBufIdx > 0) {
				fOutputStream.write(fBuf, 0, fBufIdx);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void writeInt(int val) throws DBWriteException {
		int type = -1;
		byte tmp[] = new byte[5];
		if (val < 0) {
			if (val >= -0x000000FF) {
				type = TYPE_INT_8;
				tmp[0] = TYPE_INT_8;
				tmp[1] = (byte)val;
			} else if (val >= -0x0000FFFF) {
				type = TYPE_INT_16;
				tmp[0] = TYPE_INT_16;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
			} else if (val >= -0x00FFFFFF) {
				type = TYPE_INT_24;
				tmp[0] = TYPE_INT_24;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
			} else { 
				type = TYPE_INT_32;
				tmp[0] = TYPE_INT_32;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
			}
		} else {
			if (val <= 0x0000007F) {
				type = TYPE_INT_8;
				tmp[0] = TYPE_INT_8;
				tmp[1] = (byte)val;
			} else if (val <= 0x00007FFF) {
				type = TYPE_INT_16;
				tmp[0] = TYPE_INT_16;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
			} else if (val <= 0x007FFFFF) {
				type = TYPE_INT_24;
				tmp[0] = TYPE_INT_24;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
			} else {
				type = TYPE_INT_32;
				tmp[0] = TYPE_INT_32;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
			}
		}
		writeRawBytes(tmp, 0, (type-TYPE_INT_8)+2);
		
//		writeRawString("I<" + Integer.toHexString(val) + ">");
	}
	
	public void writeBool(boolean v) throws DBWriteException {
		writeRawType((v)?TYPE_BOOL_TRUE:TYPE_BOOL_FALSE);
	}
	
	private void writeRawByte(byte data) throws DBWriteException {
		if ((fBufIdx+1) >= fBuf.length) {
			// flush before adding
			try {
				fOutputStream.write(fBuf, 0, fBufIdx);
			} catch (IOException e) {
				e.printStackTrace();
			}
			fBufIdx = 0;
		}
		fBuf[fBufIdx++] = data;
	}
	
	private void writeRawBytes(byte data[], int offset, int length) throws DBWriteException {
		if ((length+fBufIdx) >= fBuf.length) {
			// flush before adding
			try {
				if (fBufIdx > 0) {
					fOutputStream.write(fBuf, 0, fBufIdx);
				}
				fOutputStream.write(data, offset, length);
			} catch (IOException e) {
				e.printStackTrace();
			}
			fBufIdx = 0;
		} else {
			System.arraycopy(data, offset, fBuf, fBufIdx, length);
			fBufIdx += length;
		}
	}
	
	private void writeRawType(int type) throws DBWriteException {
		writeRawByte((byte)type);
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
		int type = -1;
		byte tmp[] = new byte[9];
		if (val < 0) {
			if (val >= -0x00000000000000FFL) {
				type = TYPE_INT_8;
				tmp[0] = TYPE_INT_8;
				tmp[1] = (byte)val;
			} else if (val >= -0x000000000000FFFFL) {
				type = TYPE_INT_16;
				tmp[0] = TYPE_INT_16;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
			} else if (val >= -0x0000000000FFFFFFL) {
				type = TYPE_INT_24;
				tmp[0] = TYPE_INT_24;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
			} else if (val >= -0x00000000FFFFFFFFL) {
				type = TYPE_INT_32;
				tmp[0] = TYPE_INT_32;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
			} else if (val >= -0x000000FFFFFFFFFFL) {
				type = TYPE_INT_40;
				tmp[0] = (byte)type;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
			} else if (val >= -0x0000FFFFFFFFFFFFL) {
				type = TYPE_INT_48;
				tmp[0] = (byte)type;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
			} else if (val >= -0x00FFFFFFFFFFFFFFL) {
				type = TYPE_INT_56;
				tmp[0] = (byte)type;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
				tmp[7] = (byte)(val >> 48);
			} else {
				type = TYPE_INT_64;
				tmp[0] = (byte)type;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
				tmp[7] = (byte)(val >> 48);
				tmp[8] = (byte)(val >> 56);
			}
		} else {
			if (val <= 0x000000000000007FL) {
				type = TYPE_INT_8;
				tmp[0] = TYPE_INT_8;
				tmp[1] = (byte)val;
			} else if (val <= 0x0000000000007FFFL) {
				type = TYPE_INT_16;
				tmp[0] = TYPE_INT_16;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
			} else if (val <= 0x00000000007FFFFFL) {
				type = TYPE_INT_24;
				tmp[0] = TYPE_INT_24;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
			} else if (val <= 0x000000007FFFFFFFL) {
				type = TYPE_INT_32;
				tmp[0] = TYPE_INT_32;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
			} else if (val <= 0x0000007FFFFFFFFFL) {
				type = TYPE_INT_40;
				tmp[0] = TYPE_INT_40;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
			} else if (val <= 0x00007FFFFFFFFFFFL) {
				type = TYPE_INT_48;
				tmp[0] = TYPE_INT_48;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
			} else if (val <= 0x007FFFFFFFFFFFFFL) {
				type = TYPE_INT_56;
				tmp[0] = TYPE_INT_56;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
				tmp[7] = (byte)(val >> 48);
			} else {
				type = TYPE_INT_64;
				tmp[0] = TYPE_INT_64;
				tmp[1] = (byte)val;
				tmp[2] = (byte)(val >> 8);
				tmp[3] = (byte)(val >> 16);
				tmp[4] = (byte)(val >> 24);
				tmp[5] = (byte)(val >> 32);
				tmp[6] = (byte)(val >> 40);
				tmp[7] = (byte)(val >> 48);
				tmp[8] = (byte)(val >> 56);
			}
		}
		writeRawBytes(tmp, 0, (type-TYPE_INT_8)+2);
	}

	public void writeString(String val) throws DBWriteException {
		if (val == null) {
			writeRawType(TYPE_NULL);
		} else {
			if (fDebugEn) {
				debug("    writeString: " + val);
			}
			byte b[] = val.getBytes();
			writeRawType(TYPE_STRING);
			writeInt(b.length);
			writeRawBytes(b, 0, b.length);
		}
	}

	public void writeByteArray(byte data[]) throws DBWriteException {
		if (data == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_BYTE_ARRAY);
			writeInt(data.length);
			writeRawBytes(data, 0, data.length);
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
