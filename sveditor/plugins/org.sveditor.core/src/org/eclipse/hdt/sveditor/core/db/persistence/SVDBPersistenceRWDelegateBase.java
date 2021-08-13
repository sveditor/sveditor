/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

@SuppressWarnings("rawtypes")
public abstract class SVDBPersistenceRWDelegateBase extends SVDBPersistenceRWBase 
		implements ISVDBPersistenceRWDelegate {
	protected Set<SVDBItemType>						fSupportedItems;
	protected Set<Class<?>>							fSupportedObjects;
	protected ISVDBPersistenceRWDelegateParent		fParent; 
	
	public SVDBPersistenceRWDelegateBase() {
		fSupportedItems = new HashSet<SVDBItemType>();
		fSupportedObjects = new HashSet<Class<?>>();
	}

	public void init(
			ISVDBPersistenceRWDelegateParent	parent, 
			DataInput 							in,
			DataOutput 							out) {
		fParent = parent;
		fIn = in;
		fOut = out;
	}

	public void init(Set<SVDBItemType> supported_items,
			Set<Class<?>> supported_objects) {
		fSupportedItems.addAll(supported_items);
		fSupportedObjects.addAll(supported_objects);
	}
	
	public void addSupportedType(SVDBItemType t) {
		fSupportedItems.add(t);
	}

	public Set<Class<?>> getSupportedObjects() {
		return fSupportedObjects;
	}

	public Set<Class<?>> getSupportedEnumTypes() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<SVDBItemType> getSupportedItemTypes() {
		return fSupportedItems;
	}
	
}
