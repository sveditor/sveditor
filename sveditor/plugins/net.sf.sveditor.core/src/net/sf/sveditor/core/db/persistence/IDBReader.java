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

import java.io.DataInput;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public interface IDBReader {
	
	void init(DataInput in);
	
	void setDebugEn(boolean en);
	
	int readInt() throws DBFormatException;
	
	long readLong() throws DBFormatException;
	
	void readObject(ISVDBChildItem parent, Class cls, Object obj) throws DBFormatException;
	
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
