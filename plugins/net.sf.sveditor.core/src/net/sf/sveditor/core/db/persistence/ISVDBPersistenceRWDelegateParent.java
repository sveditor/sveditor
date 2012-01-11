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
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;

public interface ISVDBPersistenceRWDelegateParent {
	
	void init(DataInput in);
	
	void init(DataOutput out);

	void writeObject(Class cls, Object obj) throws DBWriteException;

	void readObject(ISVDBChildItem parent, Class cls, Object obj) throws DBFormatException;

	SVDBLocation readSVDBLocation() throws DBFormatException;

	String readString() throws DBFormatException;

	int readRawType() throws DBFormatException;

	Map<String, String> readMapStringString() throws DBFormatException;

	Map<String, List> readMapStringList(Class val_c) throws DBFormatException;
	
	List<Long> readLongList() throws DBFormatException;

	List<Integer> readIntList() throws DBFormatException;
	
	List<String> readStringList() throws DBFormatException;
	
	List readObjectList(ISVDBChildParent parent, Class val_c) throws DBWriteException, DBFormatException;
	
	byte[] readByteArray() throws DBFormatException;
	
	boolean readBoolean() throws DBFormatException;
	
	long readLong() throws DBFormatException;

	SVDBItemType readItemType() throws DBFormatException;
	
	ISVDBItemBase readSVDBItem(ISVDBChildItem parent) throws DBFormatException;
	
	List readItemList(ISVDBChildItem parent) throws DBFormatException;

	Enum readEnumType(Class enum_type) throws DBFormatException;

	int readInt() throws DBFormatException;
	
	void writeBoolean(boolean v) throws DBWriteException;
	
	void writeRawType(int type) throws DBWriteException;
	
	void writeIntList(List<Integer> items) throws DBWriteException;

	void writeMapStringString(Map<String, String> map) throws DBWriteException;
	
	void writeMapStringList(Map<String, List> map, Class list_c) 
			throws DBWriteException, DBFormatException;
	
	void writeStringList(List<String> items) throws DBWriteException;
	
	void writeSVDBItem(ISVDBItemBase item) throws DBWriteException;
	
	void writeItemList(List items) throws DBWriteException;
	
	void writeObjectList(List items, Class obj_c) throws DBWriteException;
	
	void writeLongList(List<Long> items) throws DBWriteException;
	
	void writeSVDBLocation(SVDBLocation loc) throws DBWriteException;
	
	void writeString(String val) throws DBWriteException;
	
	void writeInt(int val) throws DBWriteException;
	
	void writeLong(long val) throws DBWriteException;
	
	void writeEnumType(Class enum_type, Enum enum_val) throws DBWriteException;
	
	void writeItemType(SVDBItemType type) throws DBWriteException;
	
	void writeByteArray(byte[] data) throws DBWriteException;
	
}
