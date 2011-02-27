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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBModIfcInstItem extends SVDBFieldItem {
	
	private SVDBTypeInfo				fTypeInfo;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBModIfcInstItem(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.ModIfcInst); 
	}
	
	public SVDBModIfcInstItem(SVDBTypeInfo type, String name) {
		super(name, SVDBItemType.ModIfcInst);
		fTypeInfo = type;
	}
	
	public SVDBModIfcInstItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fTypeInfo = SVDBTypeInfo.readTypeInfo(reader);
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVDBTypeInfo.writeTypeInfo(fTypeInfo, writer);
	}
	
	public String getTypeName() {
		if (fTypeInfo == null) {
			return "NULL";
		} else {
			return fTypeInfo.getName();
		}
	}
	
	public SVDBModIfcInstItem duplicate() {
		SVDBModIfcInstItem ret = new SVDBModIfcInstItem(fTypeInfo, getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(ISVDBItemBase other) {
		super.init(other);
		
		SVDBModIfcInstItem o = (SVDBModIfcInstItem)other;
		if (o.fTypeInfo == null) {
			fTypeInfo = null; 
		} else {
			fTypeInfo = o.fTypeInfo.duplicate();
		}
	}
}
