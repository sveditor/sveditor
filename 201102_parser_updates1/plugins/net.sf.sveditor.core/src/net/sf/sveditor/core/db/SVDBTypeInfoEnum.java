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
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoEnum extends SVDBTypeInfo {
	private List<Tuple<String, String>>			fEnumList;
	
	public SVDBTypeInfoEnum(String typename) {
		super(typename, SVDBDataType.Enum);
		fEnumList = new ArrayList<Tuple<String,String>>();
	}

	public SVDBTypeInfoEnum(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.Enum, parent, type, reader);
		
		fEnumList = new ArrayList<Tuple<String,String>>();
		int size = reader.readInt();
		for (int i=0; i<size; i++) {
			String k = reader.readString();
			String v = reader.readString();
			addEnumValue(k, v);
		}
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeInt(fEnumList.size());
		for (int i=0; i<fEnumList.size(); i++) {
			String k = fEnumList.get(i).first();
			String v = fEnumList.get(i).second();
			writer.writeString(k);
			writer.writeString(v);
		}
	}

	public List<Tuple<String, String>> getEnumValues() {
		return fEnumList;
	}
	
	public void addEnumValue(String key, String val) {
		if (val == null) {
			/*
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
			 */
			val = "";
		}
		if (key == null) {
			/*
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
			 */
			key = "";
		}
		fEnumList.add(new Tuple<String, String>(key, val));
	}
	
	public String toString() {
		return getName();
	}
	
	public SVDBTypeInfoEnum duplicate() {
		SVDBTypeInfoEnum ret = new SVDBTypeInfoEnum(getName());
		
		for (Tuple<String, String> t : fEnumList) {
			ret.addEnumValue(t.first(), t.second());
		}
		
		return ret;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoEnum) {
			SVDBTypeInfoEnum o = (SVDBTypeInfoEnum)obj;
			
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
			
			return super.equals(obj);
		}
		return false;
	}
}
