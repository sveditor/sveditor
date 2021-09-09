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

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.sveditor.core.db.SVDBItemType;

@SuppressWarnings("rawtypes")
public abstract class JITPersistenceDelegateBase extends SVDBPersistenceRWDelegateBase {
	protected List<Class<?>>				fObjectTypeList;
	
	public JITPersistenceDelegateBase() {
		fObjectTypeList = new ArrayList<Class<?>>();
	}
	
	public void setSupportedClasses(List<Class<?>> s) {
		fObjectTypeList = s;
	}
	
	@Override
	public void init(Set<SVDBItemType> supported_items,
			Set<Class<?>> supported_objects) {
		super.init(supported_items, supported_objects);
	}

	// These methods are called from outside, based on 
	// our advertised support for objects/enums
		
	public void writeEnumType(Class cls, Enum value) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	protected void writeObjectErr(Object obj) throws DBWriteException {
		System.out.println("[WRITE] Failed to find class " + obj.getClass().getName());
	}
	protected void readObjectErr(Object obj) throws DBFormatException {
		System.out.println("[READ] Failed to find class " + obj.getClass().getName());
	}
}
