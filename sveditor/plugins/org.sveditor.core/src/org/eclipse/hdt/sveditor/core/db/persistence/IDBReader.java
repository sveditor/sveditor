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

import java.io.DataInput;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public interface IDBReader {
	
	void init(DataInput in);
	
	void setDebugEn(boolean en);
	
	int readInt() throws DBFormatException;
	
	long readLong() throws DBFormatException;
	
	void readObject(ISVDBChildItem parent, Class<?> cls, Object obj) throws DBFormatException;
	
	byte [] readByteArray() throws DBFormatException;
	
	String readString() throws DBFormatException;
	
	SVDBItemType readItemType() throws DBFormatException;
	
	
	@SuppressWarnings("rawtypes")
	Enum readEnumType(Class enum_type) throws DBFormatException;
	
	@SuppressWarnings("rawtypes")
	List readItemList(ISVDBChildItem parent) throws DBFormatException;
	
	ISVDBItemBase readSVDBItem(ISVDBChildItem parent) throws DBFormatException;
	
	List<String> readStringList() throws DBFormatException;
	
	List<Integer> readIntList() throws DBFormatException;

	List<Long> readLongList() throws DBFormatException;

}
