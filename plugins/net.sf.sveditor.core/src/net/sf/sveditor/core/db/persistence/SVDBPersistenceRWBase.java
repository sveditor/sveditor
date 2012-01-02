package net.sf.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVDBPersistenceRWBase implements IDBPersistenceTypes {
	private byte									fTmp[];
	private DataInput								fInBuf;
	private DataOutput								fBuf;

	public void init(DataInput in) {
		fInBuf = in;
		fBuf = null;
	}
	
	public void init(DataOutput out) {
		fBuf = out;
		fInBuf = null;
	}
	
	public SVDBLocation readSVDBLocation() throws DBFormatException {
		int type = readRawType();
		
		if (type == TYPE_NULL) {
			return null;
		}
		
		if (type != TYPE_SVDB_LOCATION) {
			throw new DBFormatException("Expecting TYPE_SVDB_LOCATION ; received " + type);
		}


		int line = readInt();
		int pos  = readInt();

		return new SVDBLocation(line, pos);
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
			fInBuf.readFully(fTmp, 0, len);
		} catch (IOException e) {
			throw new DBFormatException("readString failed: " + e.getMessage());
		}

		String ret = new String(fTmp, 0, len);
		
		return ret;
	}

	public int readRawType() throws DBFormatException {
		int ret = -1;
		if (fInBuf == null) {
			throw new DBFormatException("fInBuf==null ; fBuf==" + fBuf);
		}
		try {
			ret = fInBuf.readByte();
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
			fInBuf.readFully(ret);
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
					ret = fInBuf.readByte();
					break;
				case TYPE_INT_16:
					ret = fInBuf.readShort();
					break;
				case TYPE_INT_32:
					ret = fInBuf.readInt();
					break;
				case TYPE_INT_64:
					ret = fInBuf.readLong();
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
					ret = fInBuf.readByte();
					break;
				case TYPE_INT_16:
					ret = fInBuf.readShort();
					break;
				case TYPE_INT_32:
					ret = fInBuf.readInt();
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

	public void writeSVDBLocation(SVDBLocation loc) throws DBWriteException {
		if (loc == null) {
			writeRawType(TYPE_NULL);
		} else {
			writeRawType(TYPE_SVDB_LOCATION);
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
				fBuf.writeBytes(val);
			} catch (IOException e) {
				throw new DBWriteException("writeString failed: " + e.getMessage());
			}
		}
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

	public void writeByteArray(byte[] data) throws DBWriteException {
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

}
