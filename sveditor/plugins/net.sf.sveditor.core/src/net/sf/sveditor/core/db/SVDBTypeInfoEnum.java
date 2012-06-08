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


package net.sf.sveditor.core.db;

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

	/*
	public Tuple<List<String>, List<String>> getEnumValues() {
		return new Tuple<List<String>, List<String>>(fKeyList, fValList);
	}
	
	public void addEnumValue(String key, String val) {
		if (val == null) {
			val = "";
		}
		if (key == null) {
			key = "";
		}
		fKeyList.add(key);
		fValList.add(val);
	}
	 */
	
	public String toString() {
		return getName();
	}
}
