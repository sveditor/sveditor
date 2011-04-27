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

import net.sf.sveditor.core.Tuple;

public class SVDBTypeInfoEnum extends SVDBTypeInfo {
	private List<String>						fKeyList;
	private List<String>						fValList;
	
	public SVDBTypeInfoEnum() {
		this("");
		fKeyList = new ArrayList<String>();
		fValList = new ArrayList<String>();
	}
	
	public SVDBTypeInfoEnum(String typename) {
		super(typename, SVDBItemType.TypeInfoEnum);
		fKeyList = new ArrayList<String>();
		fValList = new ArrayList<String>();
	}

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
	
	public String toString() {
		return getName();
	}
	
	public SVDBTypeInfoEnum duplicate() {
		return (SVDBTypeInfoEnum)super.duplicate();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoEnum) {
			SVDBTypeInfoEnum o = (SVDBTypeInfoEnum)obj;
			
			/*
			if (o.fEnumList.size() == fEnumList.size()) {
				for (int i=0; i<fEnumList.size(); i++) {
					String k1 = fEnumList.get(i).first();
					String v1 = fEnumList.get(i).second();
					String k2 = o.fEnumList.get(i).first();
					String v2 = o.fEnumList.get(i).second();
					
					if (k1 == null || k2 == null || v1 == null || v2 == null) {
						System.out.println("k1=" + k1 + " k2=" + k2 + " v1=" + v1 + " v2=" + v2);
					}
					if (!k1.equals(k2) || !v1.equals(v2)) {
						return false;
					}
				}
			} else {
				return false;
			}
			 */
			
			return super.equals(obj);
		}
		return false;
	}
}
