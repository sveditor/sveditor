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

import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public interface IDBWriter {
	
	void writeInt(int val);
	
	void writeLong(long val);
	
	void writeByteArray(byte data[]);
	
	void writeString(String val);
	
	void writeItemType(SVDBItemType type);
	
	@SuppressWarnings("unchecked")
	void writeItemList(Collection items);
	
	void writeStringList(List<String> items);
	
	void writeIntList(List<Integer> items);
	
}
