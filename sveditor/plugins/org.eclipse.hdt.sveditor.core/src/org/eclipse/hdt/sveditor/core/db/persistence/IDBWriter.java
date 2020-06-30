/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.persistence;

import java.io.DataOutput;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

@SuppressWarnings("rawtypes")
public interface IDBWriter {
	
	void init(DataOutput out);
	
	void setDebugEn(boolean en);

	void close();
	
	void writeInt(int val) throws DBWriteException;
	
	void writeLong(long val) throws DBWriteException;
	
	void writeObject(Class<?> cls, Object obj) throws DBWriteException;
	
	void writeByteArray(byte data[]) throws DBWriteException;
	
	void writeString(String val) throws DBWriteException;
	
	void writeItemType(SVDBItemType type) throws DBWriteException;
	
	void writeEnumType(Class<?> enum_type, Enum<?> value) throws DBWriteException;
	
	void writeItemList(List items) throws DBWriteException;
	
	void writeMapStringList(Map<String, List> map, Class list_c) throws DBWriteException, DBFormatException;
	
	void writeMapStringObject(Map<String, Object> map, Class list_c) throws DBWriteException, DBFormatException;
	
	void writeSVDBItem(ISVDBItemBase item) throws DBWriteException;
	
	void writeStringList(List<String> items) throws DBWriteException;
	
	void writeIntList(List<Integer> items) throws DBWriteException;

	void writeLongList(List<Long> items) throws DBWriteException;

}
