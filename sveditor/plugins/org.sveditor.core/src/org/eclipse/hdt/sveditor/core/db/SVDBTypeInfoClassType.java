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


package org.eclipse.hdt.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBTypeInfoClassType extends SVDBTypeInfoClassItem {
	public List<SVDBTypeInfoClassItem>		fTypeInfo;
	
	public SVDBTypeInfoClassType() {
		this("");
	}
	
	public SVDBTypeInfoClassType(String name) {
		super(name, SVDBItemType.TypeInfoClassType);
	}
	
	public boolean isScoped() {
		return (fTypeInfo != null && fTypeInfo.size() > 0);
	}
	
	public void addClassItem(SVDBTypeInfoClassItem item) {
		// Push the data from this item onto the list
		// Set this to the info in the item class
		SVDBTypeInfoClassItem this_i = new SVDBTypeInfoClassItem(getName());
		this_i.init(this);
		
		if (fTypeInfo == null) {
			fTypeInfo = new ArrayList<SVDBTypeInfoClassItem>();
		}
		fTypeInfo.add(this_i);

		// Set the leaf information to the new class-item info
		init_class_item(item);
	}

}
