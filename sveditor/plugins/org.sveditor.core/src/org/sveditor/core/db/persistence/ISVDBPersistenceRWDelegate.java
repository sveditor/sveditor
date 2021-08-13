/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.util.Set;

import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItemType;

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
