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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBTypeInfoEnum extends SVDBTypeInfo {
	public List<SVDBTypeInfoEnumerator>		fEnumerators;
	
	public SVDBTypeInfoEnum() {
		this("");
	}
	
	public SVDBTypeInfoEnum(String typename) {
		super(typename, SVDBItemType.TypeInfoEnum);
		fEnumerators = new ArrayList<SVDBTypeInfoEnumerator>();
	}
	
	public void addEnumerator(SVDBTypeInfoEnumerator e) {
		e.setParent(this);
		fEnumerators.add(e);
	}
	
	public List<SVDBTypeInfoEnumerator> getEnumerators() {
		return fEnumerators;
	}

	public String toString() {
		return getName();
	}
}
