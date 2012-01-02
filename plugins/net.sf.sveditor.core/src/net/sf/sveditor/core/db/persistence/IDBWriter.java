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
import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

@SuppressWarnings("rawtypes")
public interface IDBWriter {
	
	void init(DataOutput out);
	
	void setDebugEn(boolean en);

	void close();
	
	void writeInt(int val) throws DBWriteException;
	
	void writeLong(long val) throws DBWriteException;
	
	void writeObject(Class cls, Object obj) throws DBWriteException;
	
	void writeByteArray(byte data[]) throws DBWriteException;
	
	void writeString(String val) throws DBWriteException;
	
	void writeItemType(SVDBItemType type) throws DBWriteException;
	
	void writeEnumType(Class enum_type, Enum value) throws DBWriteException;
	
	void writeItemList(Collection items) throws DBWriteException;
	
	void writeSVDBItem(ISVDBItemBase item) throws DBWriteException;
	
	void writeStringList(List<String> items) throws DBWriteException;
	
	void writeIntList(List<Integer> items) throws DBWriteException;

	void writeLongList(List<Long> items) throws DBWriteException;

}
