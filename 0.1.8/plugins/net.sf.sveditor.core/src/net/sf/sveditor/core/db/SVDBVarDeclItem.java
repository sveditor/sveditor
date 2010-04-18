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

public class SVDBVarDeclItem extends SVDBFieldItem {
	protected SVDBTypeInfo					fTypeInfo;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBVarDeclItem(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.VarDecl); 
	}
	
	
	public SVDBVarDeclItem(SVDBTypeInfo type, String name) {
		super(name, SVDBItemType.VarDecl);
		fTypeInfo = type;
	}

	public SVDBVarDeclItem(SVDBTypeInfo type, String name, SVDBItemType itype) {
		super(name, itype);
		fTypeInfo = type;
	}
	
	public SVDBVarDeclItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		
		// The constructor doesn't load the type info 
		SVDBItemType ti = reader.readItemType();
		if (ti != SVDBItemType.TypeInfo) {
			throw new DBFormatException("Expecting type TypeInfo, received " +
					ti.toString());
		}
		fTypeInfo = new SVDBTypeInfo(file, parent, SVDBItemType.TypeInfo, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		fTypeInfo.dump(writer);
	}
	
	public String getTypeName() {
		return fTypeInfo.getName();
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	public SVDBItem duplicate() {
		SVDBVarDeclItem ret = new SVDBVarDeclItem(fTypeInfo, getName());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fTypeInfo.init(((SVDBVarDeclItem)other).fTypeInfo);
	}

}
