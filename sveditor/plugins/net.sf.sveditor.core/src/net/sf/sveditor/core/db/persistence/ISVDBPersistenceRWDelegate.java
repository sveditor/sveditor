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
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

/**
 * A persistence delegate provides implements read/write
 * functionality for certain object and/or enum types 
 * 
 * @author ballance
 *
 */
public interface ISVDBPersistenceRWDelegate {
	
	void init(
			ISVDBPersistenceRWDelegateParent 	parent,
			DataInput							in,
			DataOutput							out);
	
	Set<Class<?>> getSupportedObjects();

	Set<Class<?>> getSupportedEnumTypes();
	
	Set<SVDBItemType> getSupportedItemTypes();

	void writeObject(Class<?> cls, Object obj) throws DBWriteException;
	
	void writeSVDBItem(ISVDBItemBase item) throws DBWriteException;

	void writeEnumType(Class<?> cls, Enum<?> value) throws DBWriteException;

	void readObject(ISVDBChildItem parent, Class<?> cls, Object obj) throws DBFormatException;
	
	ISVDBItemBase readSVDBItem(SVDBItemType type, ISVDBChildItem parent) throws DBFormatException;

	Enum<?> readEnumType(Class<?> enum_type) throws DBFormatException;
}
