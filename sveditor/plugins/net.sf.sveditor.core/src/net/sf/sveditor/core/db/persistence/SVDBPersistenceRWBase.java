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
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBLocation;

public abstract class SVDBPersistenceRWBase implements IDBPersistenceTypes {
	private byte									fTmp[];
	protected DataInput								fIn;
	protected DataOutput							fOut;

	public void init(DataInput in) {
		fIn = in;
		fOut = null;
	}
	
	public void init(DataOutput out) {
		fOut = out;
		fIn = null;
	}
	
	public void close() {
	}
	
	public SVDBLocation readSVDBLocation() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_SVDB_LOCATION) {
			throw new DBFormatException("Expecting TYPE_SVDB_LOCATION ; received " + type);
		}


		int fileid = readInt();
		int line = readInt();
		int pos  = readInt();

		return new SVDBLocation(fileid, line, pos);
	}

	public String readString() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_STRING) {
			throw new DBFormatException("Expecting TYPE_STRING, received " + type);
		}
		
		int len = readInt();
		
		if (len < 0) {
			throw new DBFormatException("Received string length < 0: " + len);
		}
		if (fTmp == null || fTmp.length < len) {
			fTmp = new byte[len];
		}
		try {
			fIn.readFully(fTmp, 0, len);
		} catch (IOException e) {
			throw new DBFormatException("readString failed: " + e.getMessage());
		}

		String ret = new String(fTmp, 0, len);
		
		return ret;
	}

	public int readRawType() throws DBFormatException {
		int ret = -1;
		if (fIn == null) {
			throw new DBFormatException("fInBuf==null ; fBuf==" + fOut);
		}
		try {
			ret = fIn.readByte();
		} catch (IOException e) {
			throw new DBFormatException("readRawType failed: " + e.getMessage());
		}
		
		if (ret < TYPE_INT_8 || ret >= TYPE_MAX) {
			throw new DBFormatException("Invalid type " + ret);
		}
		return ret;
	}

	public Map<String, String> readMapStringString() throws DBFormatException {
		Map<String, String> ret = new HashMap<String, String>();
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
			String val = readString();
			ret.put(key, val);
		}
		
		return ret;
	}

	public Map<String, List> readMapStringStringList() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		Map<String, List> ret = new HashMap<String, List>();
		
		if (type != TYPE_MAP) {
			throw new DBFormatException("Expecting TYPE_MAP ; received " + type);
		}
		
		int size = readInt();
		for (int i=0; i<size; i++) {
			String key = readString();
			ret.put(key, readStringList());
		}
		
		return ret;
	}

	public Map<String, List> readMapStringIntegerList() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		Map<String, List> ret = new HashMap<String, List>();
		
		if (type != TYPE_MAP) {
			throw new DBFormatException("Expecting TYPE_MAP ; received " + type);
		}
		
		int size = readInt();
		for (int i=0; i<size; i++) {
			String key = readString();
			ret.put(key, readIntList());
		}
		
		return ret;
	}
	
	public List<Long> readLongList() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_LONG_LIST) {
			throw new DBFormatException("Expecting TYPE_LONG_LIST, received " + type);
		}
		
		int size = readInt();
		
		List<Long> ret = new ArrayList<Long>();
		for (int i=0; i<size; i++) {
			ret.add(readLong());
		}
		
		return ret;
	}
	
	public Set<Long> readLongSet() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_LONG_SET) {
			throw new DBFormatException("Expecting TYPE_LONG_SET, received " + type);
		}
		
		int size = readInt();
		
		Set<Long> ret = new HashSet<Long>();
		for (int i=0; i<size; i++) {
			ret.add(readLong());
		}
		
		return ret;
	}

	public List<Integer> readIntList() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_INT_LIST) {
			throw new DBFormatException("Expecting INT_LIST, receive " + type);
		}
		
		int size = readInt();
		
		List<Integer> ret = new ArrayList<Integer>();
		for (int i=0; i<size; i++) {
			ret.add(readInt());
		}
		
		return ret;
	}
	
	public Set<Integer> readIntSet() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_INT_SET) {
			throw new DBFormatException("Expecting INT_SET, receive " + type);
		}
		
		int size = readInt();
		
		Set<Integer> ret = new HashSet<Integer>();
		for (int i=0; i<size; i++) {
			ret.add(readInt());
		}
		
		return ret;
	}

	public List<String> readStringList() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_STRING_LIST) {
			throw new DBFormatException("Expecting TYPE_STRING_LIST, received " + type);
		}
		
		int size = readInt();
		
		List<String> ret = new ArrayList<String>();
		for (int i=0; i<size; i++) {
			ret.add(readString());
		}
		
		return ret;
	}
	
	public Set<String> readStringSet() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_STRING_SET) {
			throw new DBFormatException("Expecting TYPE_STRING_SET, received " + type);
		}
		
		int size = readInt();
		
		Set<String> ret = new HashSet<String>();
		for (int i=0; i<size; i++) {
			ret.add(readString());
		}
		
		return ret;
	}


	public byte[] readByteArray() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_BYTE_ARRAY) {
			throw new DBFormatException("Expecting TYPE_BYTE_ARRAY, received " + type);
		}
		int size = readInt();
		byte ret[] = new byte[size];

		try {
			fIn.readFully(ret);
		} catch (IOException e) {
			throw new DBFormatException("readByteArray failed: " + e.getMessage());
		}
		
		return ret;
	}

	public boolean readBoolean() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_BOOL_TRUE) {
			return true;
		} else if (type == TYPE_BOOL_FALSE) {
			return false;
		} else {
			throw new DBFormatException("Expecting BOOL_TRUE or BOOL_FALSE ; received " + type);
		}
	}

	public long readLong() throws DBFormatException {
		int type = readRawType();
		long ret = -1;
		if (type < TYPE_INT_8 || type > TYPE_INT_64) {
			throw new DBFormatException("Invalid int type " + type);
		}

		try {
			switch (type) {
				case TYPE_INT_8:
					ret = fIn.readByte();
					break;
				case TYPE_INT_16:
					ret = fIn.readShort();
					break;
				case TYPE_INT_32:
					ret = fIn.readInt();
					break;
				case TYPE_INT_64:
					ret = fIn.readLong();
					break;
			}
		} catch (IOException e) {
			throw new DBFormatException("readLong failed: " + e.getMessage());
		}
		
		return ret;
	}

	public int readInt() throws DBFormatException {
		int type = readRawType();
		int ret = -1;
		if (type < TYPE_INT_8 || type > TYPE_INT_32) {
			throw new DBFormatException("Invalid int type " + type);
		}
		
		try {
			switch (type) {
				case TYPE_INT_8:
					ret = fIn.readByte();
					break;
				case TYPE_INT_16:
					ret = fIn.readShort();
					break;
				case TYPE_INT_32:
					ret = fIn.readInt();
					break;
			}
		} catch (IOException e) {
			throw new DBFormatException("readInt failed: " + e.getMessage());
		}
		
		return ret;
	}

	public void writeBoolean(boolean v) throws DBWriteException {
		writeRawType((v)?TYPE_BOOL_TRUE:TYPE_BOOL_FALSE);
	}

	public void writeRawType(int type) throws DBWriteException {
		try {
			fOut.write((byte)type);
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
	
	public void writeIntSet(Set<Integer> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_INT_SET);
			writeInt(items.size());
		
			for (Integer i: items) {
				writeInt(i.intValue());
			}
		}
	}
	
	public void writeMapStringString(Map<String, String> map) throws DBWriteException {
		if (map == null) {
			writeRawType(TYPE_NULL);
 		} else {
 			writeRawType(TYPE_MAP);

 			writeInt(map.size());
 			for (Entry<String, String> e : map.entrySet()) {
 				writeString(e.getKey());
 				writeString(e.getValue());
 			}
 		}
	}

	public void writeMapStringStringList(Map<String, List> map) 
			throws DBWriteException, DBFormatException {
		if (map == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_MAP);
			
			writeInt(map.size());
			for (Entry<String, List> e : map.entrySet()) {
				writeString(e.getKey());
				writeStringList(e.getValue());
			}
		}
	}

	public void writeMapStringIntegerList(Map<String, List> map) 
			throws DBWriteException, DBFormatException {
		if (map == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_MAP);
			
			writeInt(map.size());
			for (Entry<String, List> e : map.entrySet()) {
				writeString(e.getKey());
				writeIntList(e.getValue());
			}
		}
	}
	
	public void writeStringList(List<String> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_STRING_LIST);
			writeInt(items.size());
		
			for (int i=0; i<items.size(); i++) {
				writeString(items.get(i));
			}
		}
	}
	
	public void writeStringSet(Set<String> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_STRING_SET);
			writeInt(items.size());
		
			for (String s : items) {
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
	
	public void writeLongSet(Set<Long> items) throws DBWriteException {
		if (items == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_LONG_SET);
			writeInt(items.size());
		
			for (Long v : items) {
				writeLong(v.longValue());
			}
		}
	}

	public void writeSVDBLocation(SVDBLocation loc) throws DBWriteException {
		if (loc == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_SVDB_LOCATION);
			writeInt(loc.getFileId());
			writeInt(loc.getLine());
			writeInt(loc.getPos());
		}
	}

	public void writeString(String val) throws DBWriteException {
		if (val == null) {
			writeRawType(TYPE_NULL);
		} else {
			try {
				writeRawType(TYPE_STRING);
				writeInt(val.length());
				fOut.writeBytes(val);
			} catch (IOException e) {
				throw new DBWriteException("writeString failed: " + e.getMessage());
			}
		}
	}

	public void writeInt(int val) throws DBWriteException {
		try {
			if (val < 0) {
				if (val >= -0x000000FF) {
					fOut.write((byte)TYPE_INT_8);
					fOut.write((byte)val);
				} else if (val >= -0x0000FFFF) {
					fOut.write((byte)TYPE_INT_16);
					fOut.writeShort((short)val);
				} else { 
					fOut.write((byte)TYPE_INT_32);
					fOut.writeInt(val);
				}
			} else {
				if (val <= 0x0000007F) {
					fOut.write((byte)TYPE_INT_8);
					fOut.write((byte)val);
				} else if (val <= 0x00007FFF) {
					fOut.write((byte)TYPE_INT_16);
					fOut.writeShort((short)val);
				} else {
					fOut.write((byte)TYPE_INT_32);
					fOut.writeInt(val);
				}
			}
		} catch (IOException e) {
			throw new DBWriteException("writeInt failed: " + e.getMessage());
		}
	}

	public void writeLong(long val) throws DBWriteException {
		try {
			if (val < 0) {
				if (val >= -0x00000000000000FFL) {
					fOut.write(TYPE_INT_8);
					fOut.writeByte((byte)val);
				} else if (val >= -0x000000000000FFFFL) {
					fOut.write(TYPE_INT_16);
					fOut.writeShort((short)val);
				} else if (val >= -0x00000000FFFFFFFFL) {
					fOut.write(TYPE_INT_32);
					fOut.writeInt((int)val);
				} else {
					fOut.write(TYPE_INT_64);
					fOut.writeLong(val);
				}
			} else {
				if (val <= 0x000000000000007FL) {
					fOut.write(TYPE_INT_8);
					fOut.writeByte((byte)val);
				} else if (val <= 0x0000000000007FFFL) {
					fOut.write(TYPE_INT_16);
					fOut.writeShort((short)val);
				} else if (val <= 0x000000007FFFFFFFL) {
					fOut.write(TYPE_INT_32);
					fOut.writeInt((int)val);
				} else {
					fOut.write(TYPE_INT_64);
					fOut.writeLong(val);
				}
			}
		} catch (IOException e) {
			throw new DBWriteException("writeLong failed: " + e.getMessage());
		}
	}

	public void writeByteArray(byte[] data) throws DBWriteException {
		if (data == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_BYTE_ARRAY);
			writeInt(data.length);
			try {
				fOut.write(data);
			} catch (IOException e) {
				throw new DBWriteException("writeByteArray failed: " + e.getMessage());
			}
		}
	}

}
